import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I=process.env.MAKEFUN_INPUT_DIR??'/input',O=process.env.MAKEFUN_OUTPUT_DIR??'/output';
const D = [[0, -1], [0, 1], [-1, 0], [1, 0]], U = 'udlr', V = 'UDLR', N = 250000;
function p(t) {
  const r = t.split('\n').filter(x => x), h = r.length;
  let w = 0; r.forEach(x => w = Math.max(w, x.length));
  const a = new Uint8Array(w * h).fill(1), g = [], b = [];
  let y = -1;
  r.forEach((s, j) => { for (let x = 0; x < s.length; x++) { const c = s[x], i = j * w + x; if (c == '#') continue; a[i] = 0; if ('.*+'.includes(c)) g.push(i); if ('$*'.includes(c)) b.push(i); if ('@+'.includes(c)) y = i; } });
  for (let j = 0; j < h; j++) for (let x = 0; x < w; x++) if (!j || !x || j == h - 1 || x == w - 1) a[j * w + x] = 1;
  return { w, h, a, g, b: b.sort((x, z) => x - z), y };
}
function lv(L) {
  const v = new Uint8Array(L.a.length), q = [...L.g];
  for (const g of L.g) v[g] = 1;
  for (let i = 0; i < q.length; i++) for (let k = 0; k < 4; k++) {
    const d = D[k][1] * L.w + D[k][0], y = q[i] - d;
    if (!L.a[y] && !L.a[y - d] && !v[y]) { v[y] = 1; q.push(y); }
  }
  return v;
}
function rg(L, occ, f, sn, st, k) {
  let lo = f, n = 0; k[n++] = f; sn[f] = st;
  while (n) { const x = k[--n]; if (x < lo) lo = x; for (let i = 0; i < 4; i++) { const q = x + D[i][1] * L.w + D[i][0]; if (!L.a[q] && !occ[q] && sn[q] != st) { sn[q] = st; k[n++] = q; } } }
  return lo;
}
function fr(L, occ, go, t) {
  const w = L.w;
  for (const a of [t, t - 1, t - w, t - w - 1]) {
    const s = [a, a + 1, a + w, a + w + 1];
    if (s.every(q => L.a[q] || occ[q]) && s.some(q => occ[q] && !go[q])) return 1;
  }
  return 0;
}
function wk(L, occ, f, t) {
  if (f == t) return '';
  const pv = new Int32Array(L.a.length).fill(-1), hw = new Array(L.a.length), q = [f];
  pv[f] = f;
  for (let i = 0; i < q.length; i++) { const x = q[i]; if (x == t) break; for (let k = 0; k < 4; k++) { const s = x + D[k][1] * L.w + D[k][0]; if (L.a[s] || occ[s] || pv[s] >= 0) continue; pv[s] = x; hw[s] = U[k]; q.push(s); } }
  if (pv[t] < 0) throw new Error('no walk');
  let s = ''; for (let x = t; x != f; x = pv[x]) s = hw[x] + s;
  return s;
}
function eo(w, f, m) { let x = f; for (const c of m.toLowerCase()) x += c == 'u' ? -w : c == 'd' ? w : c == 'l' ? -1 : 1; return x; }
function S(L) {
  const { w, a, g } = L, n = a.length, go = new Uint8Array(n), v = lv(L);
  for (const x of g) go[x] = 1;
  if (L.b.some(b => !v[b])) return null;
  const mn = (x, z) => Math.abs(x % w - z % w) + Math.abs((x / w | 0) - (z / w | 0));
  const hu = bs => { // cheapest box->goal assignment over permutations
    let be = 1 / 0;
    const rc = (i, u, s) => { if (s >= be) return; if (i == bs.length) { be = s; return; } for (let j = 0; j < bs.length; j++) if (!(u >> j & 1)) rc(i + 1, u | 1 << j, s + mn(bs[i], g[j])); };
    rc(0, 0, 0); return be;
  };
  const occ = new Uint8Array(n), sn = new Int32Array(n), mk = new Int32Array(n), k = new Int32Array(n);
  let st = 0;
  const key = (bs, lo) => { let x = lo; for (const b of bs) x = x * n + b; return x; };
  const hp = [], ls = (x, z) => x[0] < z[0] || x[0] == z[0] && (x[1] < z[1] || x[1] == z[1] && x[2] < z[2]);
  const pu = e => { let i = hp.length; hp.push(e); while (i) { const q = i - 1 >> 1; if (!ls(hp[i], hp[q])) break; [hp[i], hp[q]] = [hp[q], hp[i]]; i = q; } };
  const po = () => { const t = hp[0], l = hp.pop(); if (hp.length) { hp[0] = l; for (let i = 0;;) { let c = 2 * i + 1; if (c >= hp.length) break; if (c + 1 < hp.length && ls(hp[c + 1], hp[c])) c++; if (!ls(hp[c], hp[i])) break; [hp[i], hp[c]] = [hp[c], hp[i]]; i = c; } } return t; };
  const B = [L.b], Y = [L.y], G = [0], pa = [-1], pb = [-1], pd = [-1], bg = new Map;
  for (const b of L.b) occ[b] = 1;
  const lo0 = rg(L, occ, L.y, sn, ++st, k);
  for (const b of L.b) occ[b] = 0;
  bg.set(key(L.b, lo0), 0);
  const h0 = hu(L.b); pu([h0, h0, 0, 0]);
  let ct = 1, fd = L.b.every(b => go[b]) ? 0 : -1;
  while (hp.length && fd < 0) {
    const s = po()[3], bs = B[s], gg = G[s];
    for (const b of bs) occ[b] = 1;
    rg(L, occ, Y[s], sn, ++st, k);
    const hr = st;
    for (let i = 0; i < bs.length && fd < 0; i++) {
      const bx = bs[i];
      for (let di = 0; di < 4; di++) {
        const d = D[di][1] * w + D[di][0], t = bx + d;
        if (sn[bx - d] != hr || a[t] || occ[t] || !v[t]) continue;
        occ[bx] = 0; occ[t] = 1;
        const fz = fr(L, occ, go, t);
        let ky = -1, nx = null;
        if (!fz) { nx = bs.slice(); nx[i] = t; nx.sort((x, z) => x - z); ky = key(nx, rg(L, occ, bx, mk, ++st, k)); }
        occ[t] = 0; occ[bx] = 1;
        if (fz || bg.has(ky) && bg.get(ky) <= gg + 1) continue;
        if (B.length >= N) { for (const x of bs) occ[x] = 0; return null; }
        bg.set(ky, gg + 1);
        const ns = B.length, hh = hu(nx);
        B.push(nx); Y.push(bx); G.push(gg + 1); pa.push(s); pb.push(bx); pd.push(di);
        pu([gg + 1 + hh, hh, ct++, ns]);
        if (nx.every(b => go[b])) { fd = ns; break; }
      }
    }
    for (const x of bs) occ[x] = 0;
  }
  if (fd < 0) return null;
  const path = [];
  for (let s = fd; s; s = pa[s]) path.push(s);
  path.reverse();
  let m = '', pl = L.y, bs = L.b;
  for (const s of path) {
    const f = pb[s], di = pd[s], d = D[di][1] * w + D[di][0];
    for (const b of bs) occ[b] = 1;
    m += wk(L, occ, pl, f - d);
    for (const b of bs) occ[b] = 0;
    m += V[di]; pl = f;
    const nx = bs.slice(); nx[nx.indexOf(f)] = f + d; nx.sort((x, z) => x - z); bs = nx;
  }
  return m;
}
function rm(L) {
  const { w, a, g, b, y } = L, v = lv(L), row = y / w | 0, cu = new Uint8Array(a.length), pt = new Int32Array(a.length).fill(-1), R = [];
  for (let i = row * w; i < (row + 1) * w; i++) if (!a[i] && !v[i]) cu[i] = 1;
  if (b.some(x => cu[x])) return null;
  for (let s = 0; s < a.length; s++) {
    if (a[s] || cu[s] || pt[s] >= 0) continue;
    const sq = [s]; pt[s] = R.length;
    for (let i = 0; i < sq.length; i++) for (let k = 0; k < 4; k++) { const q = sq[i] + D[k][1] * w + D[k][0]; if (!a[q] && !cu[q] && pt[q] < 0) { pt[q] = R.length; sq.push(q); } }
    R.push({ b: [], g: [] });
  }
  for (const x of b) R[pt[x]].b.push(x);
  for (const x of g) if (pt[x] >= 0) R[pt[x]].g.push(x);
  if (g.some(x => pt[x] < 0) || R.some(r => r.b.length != r.g.length)) return null;
  return R.filter(r => r.b.length);
}
function solve(t) {
  const L = p(t), R = rm(L);
  if (!R) { const r = S(L); return r === null ? '' : r; }
  let pl = L.y, m = '';
  for (const r of R) {
    const a = L.a.slice();
    for (const o of R) if (o != r) for (const b of o.d ? o.g : o.b) a[b] = 1;
    const s = S({ w: L.w, h: L.h, a, g: r.g.slice().sort((x, z) => x - z), b: r.b.slice().sort((x, z) => x - z), y: pl });
    if (s === null) return '';
    m += s; pl = eo(L.w, pl, s); r.d = 1;
  }
  return m;
}
for (const id of readdirSync(I).sort()) {
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), solve(readFileSync(join(I, id, 'level.txt'), 'utf8')) + '\n');
}
