// Sokoban, push-optimal per room. Rooms are independent (a box out of a door
// never returns), so P* is the sum of room optima. A* over pushes per room;
// heuristic = cheapest box-to-goal assignment over reverse-push distances;
// deadlocks pruned (non-live squares, frozen 2x2). Fixed cap, no clock.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const D = [[0, -1, 'u', 'U'], [0, 1, 'd', 'D'], [-1, 0, 'l', 'L'], [1, 0, 'r', 'R']];
const INF = 1e9, CAP = 2e4;
function ps(t) {
  const r = t.split('\n').filter(x => x.length), h = r.length, w = Math.max(...r.map(x => x.length));
  const W = new Uint8Array(w * h).fill(1), G = [], B = [];
  let P = -1;
  r.forEach((row, y) => { for (let x = 0; x < row.length; x++) { const c = row[x], i = y * w + x; if (c === '#') continue; W[i] = 0; if ('.*+'.includes(c)) G.push(i); if ('$*'.includes(c)) B.push(i); if ('@+'.includes(c)) P = i; } });
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) if (!x || !y || x === w - 1 || y === h - 1) W[y * w + x] = 1;
  return { w, h, W, G, B, P };
}
function pd(w, W, G) {
  const n = W.length, ds = [], lv = new Uint8Array(n);
  for (const g of G) {
    const d = new Int32Array(n).fill(INF); d[g] = 0; lv[g] = 1;
    const q = [g];
    for (let i = 0; i < q.length; i++) { const x = q[i];
      for (const [dx, dy] of D) { const dd = dy * w + dx, y = x - dd;
        if (!W[y] && !W[y - dd] && d[y] > d[x] + 1) { d[y] = d[x] + 1; lv[y] = 1; q.push(y); } } }
    ds.push(d);
  }
  return { ds, lv };
}
function rg(w, W, oc, f, sn, st) {
  const s = [f]; sn[f] = st;
  let lo = f;
  for (let i = 0; i < s.length; i++) { const p = s[i]; if (p < lo) lo = p;
    for (const [dx, dy] of D) { const q = p + dy * w + dx;
      if (!W[q] && !oc[q] && sn[q] !== st) { sn[q] = st; s.push(q); } } }
  return lo;
}
function fz(w, W, oc, gl, t) {
  for (const a of [t, t - 1, t - w, t - w - 1]) { const b = a + 1, c = a + w, d = c + 1;
    if (!(W[a] || oc[a]) || !(W[b] || oc[b]) || !(W[c] || oc[c]) || !(W[d] || oc[d])) continue;
    if ((oc[a] && !gl[a]) || (oc[b] && !gl[b]) || (oc[c] && !gl[c]) || (oc[d] && !gl[d])) return true; }
  return false;
}
function sc(sv, gr) {
  const { w, W, G, B, P } = sv, n = W.length, m = B.length, gl = new Uint8Array(n);
  for (const g of G) gl[g] = 1;
  const { ds, lv } = pd(w, W, G);
  if (B.some(b => !lv[b])) return null;
  const he = bs => { let be = INF; const u = new Array(m).fill(0);
    const go = (i, s) => { if (s >= be) return; if (i === m) { be = s; return; }
      for (let j = 0; j < m; j++) if (!u[j]) { u[j] = 1; const d = ds[j][bs[i]]; if (d < INF) go(i + 1, s + d); u[j] = 0; } };
    go(0, 0); return be; };
  const pw = n ** m;
  const pk = bs => { let k = 0; for (const b of bs) k = k * n + b; return k; };
  const un = k => { const bs = new Array(m); for (let i = m - 1; i >= 0; i--) { bs[i] = k % n; k = Math.floor(k / n); } return bs; };
  const sn = new Int32Array(n), mk = new Int32Array(n), oc = new Uint8Array(n);
  let st = 0, ms = 0;
  for (const b of B) oc[b] = 1;
  const l0 = rg(w, W, oc, P, sn, ++st);
  const bx = [pk(B)], pl = [P], ky = [l0 * pw + bx[0]], pa = [-1], pf = [0], pt = [0], gs = [0];
  const be = new Map([[ky[0], 0]]);
  const h0 = he(B);
  if (h0 >= INF) return null;
  const hp = [];
  const ls = (a, b) => a[0] < b[0] || (a[0] === b[0] && (a[1] < b[1] || (a[1] === b[1] && a[2] < b[2])));
  const pu = e => { let i = hp.length; hp.push(e);
    while (i > 0) { const p = (i - 1) >> 1; if (!ls(hp[i], hp[p])) break; [hp[i], hp[p]] = [hp[p], hp[i]]; i = p; } };
  const po = () => { const t = hp[0], l = hp.pop();
    if (hp.length) { hp[0] = l;
      for (let i = 0;;) { let c = 2 * i + 1; if (c >= hp.length) break;
        if (c + 1 < hp.length && ls(hp[c + 1], hp[c])) c++;
        if (!ls(hp[c], hp[i])) break; [hp[i], hp[c]] = [hp[c], hp[i]]; i = c; } }
    return t; };
  let sq = 0, ex = 0;
  pu([h0, h0, sq++, 0]);
  while (hp.length) {
    const s = po()[3];
    if (be.get(ky[s]) !== s) continue;
    const g = gs[s], bs = un(bx[s]);
    if (bs.every(b => gl[b])) { const pa2 = [];
      for (let t = s; t > 0; t = pa[t]) pa2.push({ f: pf[t], t: pt[t] });
      return pa2.reverse(); }
    if (++ex > CAP) return null;
    for (const b of bs) oc[b] = 1;
    const hr = ++st;
    rg(w, W, oc, pl[s], sn, hr);
    for (let bi = 0; bi < m; bi++) { const b = bs[bi];
      for (const [dx, dy] of D) { const d = dy * w + dx, t = b + d;
        if (W[t] || oc[t] || !lv[t] || sn[b - d] !== hr) continue;
        oc[b] = 0; oc[t] = 1;
        if (fz(w, W, oc, gl, t)) { oc[t] = 0; oc[b] = 1; continue; }
        const nb = bs.slice(); nb[bi] = t; nb.sort((x, y) => x - y);
        const lo = rg(w, W, oc, b, mk, ++ms), k = lo * pw + pk(nb), g2 = g + 1, pr = be.get(k);
        if (pr !== undefined && gs[pr] <= g2) { oc[t] = 0; oc[b] = 1; continue; }
        const h = he(nb);
        if (h >= INF) { oc[t] = 0; oc[b] = 1; continue; }
        const ix = bx.length;
        be.set(k, ix); bx.push(pk(nb)); pl.push(b); ky.push(k); pa.push(s); pf.push(b); pt.push(t); gs.push(g2);
        pu([gr ? h : g2 + h, h, sq++, ix]);
        oc[t] = 0; oc[b] = 1; } }
    for (const b of bs) oc[b] = 0;
  }
  return null;
}
function wk(w, W, oc, f, t) {
  if (f === t) return '';
  const n = W.length, pv = new Int32Array(n).fill(-1), hw = new Array(n), q = [f];
  pv[f] = f;
  for (let i = 0; i < q.length; i++) { const p = q[i]; if (p === t) break;
    for (const [dx, dy, ch] of D) { const nq = p + dy * w + dx;
      if (W[nq] || oc[nq] || pv[nq] !== -1) continue;
      pv[nq] = p; hw[nq] = ch; q.push(nq); } }
  if (pv[t] === -1) throw new Error('unreachable walk');
  let s = '';
  for (let p = t; p !== f; p = pv[p]) s = hw[p] + s;
  return s;
}
function rp(w, W, B, P, ph) {
  const oc = new Uint8Array(W.length);
  for (const b of B) oc[b] = 1;
  let p = P, m = '';
  for (const { f, t } of ph) { const d = t - f;
    const dr = D.find(([dx, dy]) => dy * w + dx === d);
    if (!dr) throw new Error('bad push');
    m += wk(w, W, oc, p, f - d) + dr[3];
    oc[f] = 0; oc[t] = 1; p = f; }
  return [m, p];
}
function rm(lv) {
  const { w, W, G, B, P } = lv, { lv: li } = pd(w, W, G);
  const r = Math.floor(P / w), cut = new Uint8Array(W.length);
  for (let i = r * w; i < (r + 1) * w; i++) if (!W[i] && !li[i]) cut[i] = 1;
  if (B.some(b => cut[b])) return null;
  const pt = new Int32Array(W.length).fill(-1), R = [];
  for (let s = 0; s < W.length; s++) { if (W[s] || cut[s] || pt[s] >= 0) continue;
    const sq = [s]; pt[s] = R.length;
    for (let i = 0; i < sq.length; i++) for (const [dx, dy] of D) { const q = sq[i] + dy * w + dx;
      if (!W[q] && !cut[q] && pt[q] < 0) { pt[q] = R.length; sq.push(q); } }
    R.push({ B: [], G: [] }); }
  for (const b of B) R[pt[b]].B.push(b);
  for (const g of G) { if (pt[g] < 0) return null; R[pt[g]].G.push(g); }
  if (R.some(x => x.B.length !== x.G.length)) return null;
  return R.filter(x => x.B.length);
}
function sv(t) {
  const lv = ps(t), R = rm(lv);
  if (!R) return '';
  const cur = R.map(r => r.B.slice());
  let P = lv.P, m = '';
  for (let i = 0; i < R.length; i++) {
    const W = lv.W.slice();
    for (let j = 0; j < R.length; j++) if (j !== i) for (const b of cur[j]) W[b] = 1;
    const sub = { w: lv.w, h: lv.h, W, G: R[i].G, B: cur[i].slice(), P };
    const ph = sc(sub, false) ?? sc(sub, true);
    if (!ph) return '';
    const [mm, pp] = rp(lv.w, W, cur[i], P, ph);
    m += mm; P = pp;
    cur[i] = R[i].G.slice();
  }
  return m;
}
for (const id of readdirSync(I).sort()) {
  const m = sv(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), m + '\n');
}
