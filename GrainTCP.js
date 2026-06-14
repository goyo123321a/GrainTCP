const CFG = {
  id: '2523c510-9ff0-415b-9582-93949bfae7e3',
  chunk: 64 * 1024,        // 初始读取 buffer
  maxBuffer: 256 * 1024,   // 最大读取 buffer（dnPack * 8）
  dnPack: 32 * 1024,       // 下行合并包大小
  dnTail: 512,             // 下行合并触发剩余阈值
  dnMs: 0,                 // 下行合并延迟
  upPack: 16 * 1024,       // 上行合并包大小
  upQMax: 256 * 1024,      // 上行队列最大字节数
  maxED: 8 * 1024,         // 最大早期数据
  concur: 4,               // 并发连接数
  connectTimeout: 10000,   // 连接超时（ms）
  backpressureLimit: 256 * 1024  // 发送背压阈值
};

// 预计算 UUID 字节（直接写死，省去运行时解析）
const idB = new Uint8Array([
  0x25, 0x23, 0xc5, 0x10, 0x9f, 0xf0, 0x41, 0x5b,
  0x95, 0x82, 0x93, 0x94, 0x9b, 0xfa, 0xe7, 0xe3
]);
const [I0, I1, I2, I3, I4, I5, I6, I7, I8, I9, I10, I11, I12, I13, I14, I15] = idB;

const matchID = c =>
  c[1] === I0 && c[2] === I1 && c[3] === I2 && c[4] === I3 &&
  c[5] === I4 && c[6] === I5 && c[7] === I6 && c[8] === I7 &&
  c[9] === I8 && c[10] === I9 && c[11] === I10 && c[12] === I11 &&
  c[13] === I12 && c[14] === I13 && c[15] === I14 && c[16] === I15;

const addr = (t, b) => {
  if (t === 1) return `${b[0]}.${b[1]}.${b[2]}.${b[3]}`;
  if (t === 3) {
    const dec = new TextDecoder();   // 惰性创建，避免常驻
    return dec.decode(b);
  }
  return `[${Array.from({ length: 8 }, (_, i) =>
    ((b[i * 2] << 8) | b[i * 2 + 1]).toString(16)
  ).join(':')}]`;
};

const sprout = (f, h, p, s = f.connect({ hostname: h, port: p })) =>
  s.opened.then(() => s);

const raceSprout = (f, h, p) => {
  if (!f?.connect) return Promise.reject(new Error('connect unavailable'));
  if (CFG.concur <= 1) return sprout(f, h, p);
  const ts = Array(CFG.concur).fill().map(() => sprout(f, h, p));
  // 加入超时竞速
  const timeout = new Promise((_, reject) =>
    setTimeout(() => reject(new Error('connect timeout')), CFG.connectTimeout)
  );
  return Promise.any([...ts, timeout]).then(w => {
    ts.forEach(t => t.then(s => s !== w && s.close(), () => {}));
    return w;
  });
};

const parseAddr = (b, o, t) => {
  const l = t === 3 ? b[o++] : t === 1 ? 4 : t === 4 ? 16 : null;
  if (l === null) return null;
  const n = o + l;
  return n > b.length ? null : { targetAddrBytes: b.subarray(o, n), dataOffset: n };
};

const vless = c => {
  if (c.length < 24 || !matchID(c)) return null;
  let o = 19 + c[17];
  const p = (c[o] << 8) | c[o + 1];
  let t = c[o + 2];
  if (t !== 1) t += 1;
  const a = parseAddr(c, o + 3, t);
  return a ? { addrType: t, ...a, port: p } : null;
};

// 上行队列（保持不变）
const mkQ = (cap, qCap = cap, itemsMax = Math.max(1, qCap >> 8)) => {
  let q = [], h = 0, qB = 0, buf = null;
  const trim = () => { h > 32 && h * 2 >= q.length && (q = q.slice(h), h = 0); };
  const take = () => { if (h >= q.length) return null; const d = q[h]; q[h++] = undefined; qB -= d.byteLength; trim(); return d; };
  return {
    get bytes() { return qB; }, get size() { return q.length - h; },
    get empty() { return h >= q.length; }, clear() { q = []; h = 0; qB = 0; },
    sow(d) { const n = d?.byteLength || 0; if (!n) return 1; if (qB + n > qCap || q.length - h >= itemsMax) return 0; q.push(d); qB += n; return 1; },
    bundle(d) {
      d ||= take(); if (!d || h >= q.length || d.byteLength >= cap) return [d, 0];
      let n = d.byteLength, e = h;
      while (e < q.length) { const x = q[e], nn = n + x.byteLength; if (nn > cap) break; n = nn; e++; }
      if (e === h) return [d, 0];
      const out = buf ||= new Uint8Array(cap); out.set(d);
      for (let o = d.byteLength; h < e;) { const x = q[h]; q[h++] = undefined; qB -= x.byteLength; out.set(x, o); o += x.byteLength; }
      trim(); return [out.subarray(0, n), 1];
    }
  };
};

// 下行合并队列（保持不变）
const mkDn = w => {
  const cap = CFG.dnPack, tail = CFG.dnTail, low = Math.max(4096, tail << 3);
  let pb = new Uint8Array(cap), p = 0, tp = 0, mq = 0, gen = 0, qk = 0, qr = 0;
  const reap = () => { tp && clearTimeout(tp); tp = 0; mq = 0; if (!p) return; w.send(pb.subarray(0, p).slice()); pb = new Uint8Array(cap); p = 0; qr = 0; };
  const ripen = () => {
    if (tp || mq) return; mq = 1; qk = gen;
    queueMicrotask(() => {
      mq = 0; if (!p || tp) return; if (cap - p < tail) return reap();
      tp = setTimeout(() => {
        tp = 0; if (!p) return; if (cap - p < tail) return reap();
        if (qr < 2 && (gen !== qk || p < low)) { qr++; qk = gen; return ripen(); }
        reap();
      }, Math.max(CFG.dnMs, 1));
    });
  };
  return {
    send(u) {
      let o = 0, n = u?.byteLength || 0; if (!n) return;
      while (o < n) {
        if (!p && n - o >= cap) { const m = Math.min(cap, n - o); w.send(o || m !== n ? u.subarray(o, o + m) : u); o += m; continue; }
        const m = Math.min(cap - p, n - o); pb.set(u.subarray(o, o + m), p); p += m; o += m; gen++;
        if (p === cap || cap - p < tail) reap(); else ripen();
      }
    }, reap
  };
};

// 自适应读取的 mill（带背压控制）
const mill = async (rd, w) => {
  const r = rd.getReader({ mode: 'byob' });
  const tx = mkDn(w);
  let bufferSize = CFG.chunk;
  let buf = new ArrayBuffer(bufferSize);

  try {
    for (;;) {
      // 背压控制：发送缓冲区超过阈值时等待
      while (w.bufferedAmount > CFG.backpressureLimit) {
        await new Promise(resolve => setTimeout(resolve, 10));
      }

      const { done, value: v } = await r.read(new Uint8Array(buf, 0, bufferSize));
      if (done) break;
      if (!v?.byteLength) continue;

      // 根据数据大小决定直接发送还是加入合并队列
      if (v.byteLength >= (bufferSize >> 1)) {
        tx.reap();
        w.send(v);
      } else {
        // 直接传入 v，不再 .slice()，内部会安全 subarray 并复制
        tx.send(v);
      }

      // 自适应调整下一次读取的 buffer 大小
      if (v.byteLength === bufferSize && bufferSize < CFG.maxBuffer) {
        bufferSize = Math.min(bufferSize * 2, CFG.maxBuffer);
      } else if (v.byteLength < bufferSize / 4 && bufferSize > CFG.chunk) {
        bufferSize = Math.max(CFG.chunk, Math.floor(bufferSize / 2));
      }
      buf = new ArrayBuffer(bufferSize);
    }
    tx.reap();
  } catch {}
  finally {
    try { tx.reap(); } catch {}
    try { r.releaseLock(); } catch {}
  }
};

const ws = async req => {
  const [client, server] = Object.values(new WebSocketPair());
  server.accept({ allowHalfOpen: true });
  server.binaryType = 'arraybuffer';
  const fetcher = req.fetcher;

  const edStr = req.headers.get('sec-websocket-protocol');
  const ed = edStr && edStr.length <= CFG.maxED * 4 / 3 + 4
    ? /** @type {*} */ (Uint8Array).fromBase64(edStr, { alphabet: 'base64url' })
    : null;

  let curW = null, sock = null, closed = false, busy = false;
  const uq = mkQ(CFG.upPack, CFG.upQMax, CFG.upQMax >> 8);

  const wither = () => {
    if (closed) return;
    closed = true;
    uq.clear();
    try { curW?.releaseLock(); } catch {}
    try { sock?.close(); } catch {}
    try { server.close(1000, 'ok'); } catch {}  // 规范关闭码
  };

  const toU8 = d => d instanceof Uint8Array ? d
    : ArrayBuffer.isView(d) ? new Uint8Array(d.buffer, d.byteOffset, d.byteLength)
    : new Uint8Array(d);

  const sow = d => {
    const u = toU8(d), n = u.byteLength;
    if (!n) return 1;
    if (uq.sow(u)) return 1;
    wither();
    return 0;
  };

  const thresh = async () => {
    if (busy || closed) return;
    busy = true;
    try {
      for (;;) {
        if (closed) break;
        if (!sock) {
          const [d] = uq.bundle();
          if (!d) break;
          const r = vless(d);
          if (!r) throw wither();
          server.send(new Uint8Array([d[0], 0]));  // 回复 VLESS 响应头
          const host = addr(r.addrType, r.targetAddrBytes),
                port = r.port,
                payload = d.subarray(r.dataOffset);
          sock = await raceSprout(fetcher, host, port);
          if (!sock) throw wither();
          curW = sock.writable.getWriter();
          // 写入首包剩余数据
          const [first] = uq.bundle(payload);
          first?.byteLength && await curW.write(first);
          mill(sock.readable, server).finally(() => wither());
          continue;
        }
        const [d] = uq.bundle();
        if (!d) break;
        // 写入远程，短暂拥塞时重试一次
        try { await curW.write(d); } catch {
          await new Promise(r => setTimeout(r, 50));
          try { await curW.write(d); } catch { throw wither(); }
        }
      }
    } catch { wither(); }
    finally {
      busy = false;
      !uq.empty && !closed && queueMicrotask(thresh);
    }
  };

  if (ed && sow(ed)) thresh();

  server.addEventListener('message', e => { closed || (sow(e.data) && thresh()); });
  server.addEventListener('close', () => wither());
  server.addEventListener('error', () => wither());

  return new Response(null, {
    status: 101,
    webSocket: client,
    headers: { 'Sec-WebSocket-Extensions': '' }
  });
};

export default { fetch: req => req.headers.get('Upgrade')?.toLowerCase() === 'websocket' ? ws(req) : new Response('Hello world!') };
