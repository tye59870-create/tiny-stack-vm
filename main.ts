// tiny-stack-vm: a compact, exact interpreter of make.fun's tiny stack ISA v1.
// Reads /input/<id>/{program.bin,input.bin}, writes /output/<id>/{stdout.bin,exit.txt}.
// Node 22 runs this file as-is (plain JavaScript, erasable-syntax-free).
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcode table: for byte b, char code c = 1 + immCode*16 + pops*4 + pushes (0 = no opcode).
// immCode: imm 0 -> 0, 1 -> 1, 2 -> 2, 4 -> 3. Covers bytes 0x00..0x53.
// Immediate lengths by immCode, hoisted so the hot loop never allocates.
const IMM = [0, 1, 2, 4];
const T = '\x01\x122\x05\x07\x0b\x0c\x10\0\0\0\0\0\0\0\0\x0a\x0a\x0a\x0a\x0a\x0a\x0a\x06\x0a\x0a\x0a\x06\x0a\x0a\x0a\0\x0a\x0a\x0a\0\0\0\0\0\0\0\0\0\0\0\0\0!%%!\x01\0\0\0\0\0\0\0\0\0\0\0\x06\x09\0\0\0\0\0\0\0\0\0\0\0\0\0\0\x05\x05\x02\x05';

function run(p, inp) {
  const n = p.length;
  const D = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let cp = 0;
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let ol = 0, ip = 0, pc = 0, st = 0;
  const end = (code) => [out.subarray(0, ol), code];
  for (;;) {
    if (st === 1e6) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = p[pc];
    const t = T.charCodeAt(op) || 0;
    if (!t) return end(5);
    const v = t - 1;
    const im = IMM[v >> 4];
    const pops = (v >> 2) & 3;
    const push = v & 3;
    if (pc + im >= n) return end(9);
    st++;
    const nx = pc + 1 + im;
    if (sp < pops) return end(2);
    if (sp - pops + push > 256) return end(3);
    pc = nx;
    switch (op) {
      case 0x00:
        return end(0);
      case 0x01:
        D[sp++] = (p[nx - 1] << 24) >> 24;
        break;
      case 0x02:
        D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24);
        break;
      case 0x03:
        sp--;
        break;
      case 0x04:
        D[sp] = D[sp - 1];
        sp++;
        break;
      case 0x05: {
        const x = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = x;
        break;
      }
      case 0x06:
        D[sp] = D[sp - 2];
        sp++;
        break;
      case 0x07: {
        const x = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = x;
        break;
      }
      case 0x17:
        D[sp - 1] = -D[sp - 1];
        break;
      case 0x1b:
        D[sp - 1] = ~D[sp - 1];
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r;
        switch (op) {
          case 0x10: r = a + b; break;
          case 0x11: r = a - b; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13:
            if (!b) return end(4);
            r = (a / b) | 0;
            break;
          case 0x14:
            if (!b) return end(4);
            r = a % b;
            break;
          case 0x15:
            if (!b) return end(4);
            r = Math.floor((a >>> 0) / (b >>> 0));
            break;
          case 0x16:
            if (!b) return end(4);
            r = (a >>> 0) % (b >>> 0);
            break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << b; break;
          case 0x1d: r = a >> b; break;
          case 0x1e: r = a >>> b; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          case 0x22: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break;
        }
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const x = D[--sp];
          take = op === 0x31 ? x === 0 : x !== 0;
        }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33:
        if (cp === 64) return end(7);
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 0x34:
        if (!cp) return end(8);
        pc = C[--cp];
        break;
      case 0x40: {
        const a = D[sp - 1];
        if (a < 0 || a > 255) return end(6);
        D[sp - 1] = M[a];
        break;
      }
      case 0x41: {
        const a = D[sp - 1];
        const x = D[sp - 2];
        if (a < 0 || a > 255) return end(6);
        sp -= 2;
        M[a] = x;
        break;
      }
      case 0x50: {
        const s = String(D[sp - 1]);
        if (ol + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (ol + 1 > 65536) return end(11);
        out[ol++] = D[--sp] & 255;
        break;
      case 0x52:
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53:
        return end(D[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r[0]);
  writeFileSync(join(O, id, 'exit.txt'), r[1] + '\n');
}
