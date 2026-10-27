module

public import Certificates.Data.CFSGNative.YGroups.DCE.EngineB

public section

namespace CFSG.YGroups.DCE.B

@[expose] def letterTok (c : Nat) : Nat := 2 ^ 62 + c

@[expose] def tokens (b : ByteArray) : Array Nat := Id.run do
  let mut out : Array Nat := Array.mkEmpty (b.size / 3)
  let mut cur : Nat := 0
  let mut inNum := false
  for c in b do
    if 48 ≤ c.toNat && c.toNat ≤ 57 then
      cur := cur * 10 + (c.toNat - 48)
      inNum := true
    else
      if inNum then
        out := out.push cur
        cur := 0
        inNum := false
      if 65 ≤ c.toNat && c.toNat ≤ 90 then out := out.push (letterTok c.toNat)
  if inNum then out := out.push cur
  return out

@[expose] def opArity : Nat → Nat
  | 0 | 2 | 3 | 4 | 6 | 7 | 8 | 9 | 17 => 2
  | 1 | 5 | 10 | 11 => 3
  | 12 | 13 | 15 | 16 => 4
  | 14 => 12
  | _ => 0

@[expose] def mkIns (op : Nat) (a : Array Nat) : Ins :=
  let g := fun i => a[i]!
  match op with
  | 0 => .pLetter (g 0) (g 1)
  | 1 => .pMul (g 0) (g 1) (g 2)
  | 2 => .pInv (g 0) (g 1)
  | 3 => .pOfW (g 0) (g 1)
  | 4 => .wRoot (g 0) (g 1)
  | 5 => .wMul (g 0) (g 1) (g 2)
  | 6 => .wInv (g 0) (g 1)
  | 7 => .wId (g 0) (g 1)
  | 8 => .v0 (g 0) (g 1)
  | 9 => .v1 (g 0) (g 1)
  | 10 => .v2 (g 0) (g 1) (g 2)
  | 11 => .w3 (g 0) (g 1) (g 2)
  | 12 => .v4 (g 0) (g 1) (g 2) (g 3)
  | 13 => .v5 (g 0) (g 1) (g 2) (g 3)
  | 14 => .v6 (g 0) (g 1) (g 2) (g 3) (a.extract 4 12)
  | 15 => .v7 (g 0) (g 1) (g 2) (g 3)
  | 16 => .w8 (g 0) (g 1) (g 2) (g 3)
  | _ => .pOfV (g 0) (g 1)

structure Cert where
  prog : Array Ins
  words : Array (Nat × Array Nat)
  fins : Array (Nat × NodeFin)

@[inline, expose] def take (t : Array Nat) (i k : Nat) : Array Nat := t.extract i (i + k)

@[expose] def parseCert (t : Array Nat) : Cert := Id.run do
  let mut i := 1
  let mut prog : Array Ins := #[]
  for _ in [0:t.size] do
    if i < t.size && t[i]! != letterTok 78 then
      let op := t[i]!
      let k := opArity op
      prog := prog.push (mkIns op (take t (i + 1) k))
      i := i + 1 + k
    else break
  i := i + 1
  let nn := t[i]!
  i := i + 1
  let mut words : Array (Nat × Array Nat) := #[]
  for _ in [0:nn] do
    let par := t[i]!
    let len := t[i + 1]!
    words := words.push (par, take t (i + 2) len)
    i := i + 2 + len
  i := i + 1
  let nf := t[i]!
  i := i + 1
  let mut fins : Array (Nat × NodeFin) := #[]
  for _ in [0:nf] do
    let j := t[i]!
    let a := t[i + 1]!
    let fg := take t (i + 2) a
    i := i + 2 + a
    let b := t[i]!
    let cv := take t (i + 1) b
    i := i + 1 + b
    let c := t[i]!
    i := i + 1
    let mut ch : Array (Nat × Array Nat) := #[]
    for _ in [0:c] do
      let β := t[i]!
      let s := t[i + 1]!
      ch := ch.push (β, take t (i + 2) s)
      i := i + 2 + s
    fins := fins.push (j, { fgens := fg, cover := cv, chain := ch })
  return { prog := prog, words := words, fins := fins }

end CFSG.YGroups.DCE.B
