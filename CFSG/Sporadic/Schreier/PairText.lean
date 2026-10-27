module

public import Init

public section

namespace CFSG.Sporadic.Schreier.PairText

@[expose] def hexVectors (N d : Nat) (s : String) : Array (List Nat) :=
  let b := s.toUTF8
  Array.ofFn (n := N) fun i => (List.range d).map fun j =>
    let c := (b.get! (d * i.val + j)).toNat
    if c < 58 then c - 48 else c - 55

@[expose] def tokens (s : String) : Array Int := Id.run do
  let b := s.toUTF8
  let mut out : Array Int := #[]
  let mut cur : Nat := 0
  let mut neg := false
  let mut inTok := false
  for i in [0:b.size] do
    let c := (b.get! i).toNat
    if 48 ≤ c && c ≤ 57 then
      cur := cur * 10 + (c - 48)
      inTok := true
    else if c == 45 then
      neg := true
    else
      if inTok then
        out := out.push (if neg then -(cur : Int) else (cur : Int))
      cur := 0
      neg := false
      inTok := false
  if inTok then
    out := out.push (if neg then -(cur : Int) else (cur : Int))
  return out

structure ChainRec where
  gens : Array (Array Nat)
  base : List Nat
  strong : Array (Array Nat)
  words : Array (List Int)
deriving Inhabited

structure NGRec where
  rep : Array Nat
  conj : Array (List Int)
  chain : ChainRec
deriving Inhabited

structure SylowRec where
  prime : Nat
  gens : Array (Array Nat)
  records : Array NGRec
deriving Inhabited

@[expose] def tokNats (t : Array Int) (i k : Nat) : Array Nat :=
  Array.ofFn (n := k) fun j => (t[i + j.val]!).toNat

@[expose] def tokWord (t : Array Int) (i : Nat) : List Int × Nat :=
  let len := (t[i]!).toNat
  ((List.range len).map fun j => t[i + 1 + j]!, i + 1 + len)

@[expose] def tokWords (t : Array Int) (i k : Nat) : Array (List Int) × Nat := Id.run do
  let mut pos := i
  let mut out : Array (List Int) := #[]
  for _ in [0:k] do
    let r := tokWord t pos
    out := out.push r.1
    pos := r.2
  return (out, pos)

@[expose] def tokPerms (n : Nat) (t : Array Int) (i k : Nat) : Array (Array Nat) × Nat :=
  (Array.ofFn (n := k) fun j => tokNats t (i + n * j.val) n, i + n * k)

@[expose] def tokChain (n : Nat) (t : Array Int) (i : Nat) : ChainRec × Nat :=
  let cg := (t[i]!).toNat
  let cb := (t[i + 1]!).toNat
  let cs := (t[i + 2]!).toNat
  let cd := (t[i + 3]!).toNat
  let g := tokPerms n t (i + 4) cg
  let base := (tokNats t g.2 cb).toList
  let s := tokPerms n t (g.2 + cb) cs
  let w := tokWords t s.2 cd
  ({ gens := g.1, base := base, strong := s.1, words := w.1 }, w.2)

@[expose] def tokRecord (n : Nat) (t : Array Int) (i : Nat) : NGRec × Nat :=
  let rep := tokNats t i n
  let cw := tokWords t (i + n + 1) (t[i + n]!).toNat
  let ch := tokChain n t cw.2
  ({ rep := rep, conj := cw.1, chain := ch.1 }, ch.2)

@[expose] def tokSylow (n : Nat) (t : Array Int) (i : Nat) : SylowRec × Nat := Id.run do
  let p := (t[i]!).toNat
  let g := tokPerms n t (i + 2) (t[i + 1]!).toNat
  let nr := (t[g.2]!).toNat
  let mut pos := g.2 + 1
  let mut recs : Array NGRec := #[]
  for _ in [0:nr] do
    let r := tokRecord n t pos
    recs := recs.push r.1
    pos := r.2
  return ({ prime := p, gens := g.1, records := recs }, pos)

@[expose] def parseSylows (n : Nat) (t : Array Int) : Array SylowRec := Id.run do
  let mut pos := 1
  let mut out : Array SylowRec := #[]
  for _ in [0:(t[0]!).toNat] do
    let e := tokSylow n t pos
    out := out.push e.1
    pos := e.2
  return out

@[expose] def parseOrbitsMerges (t : Array Int) :
    List (List Nat) × List (Nat × List (Nat × Nat × Nat)) := Id.run do
  let mut pos := 1
  let mut orbs : Array (List Nat) := #[]
  for _ in [0:(t[0]!).toNat] do
    let sz := (t[pos]!).toNat
    orbs := orbs.push (tokNats t (pos + 1) sz).toList
    pos := pos + 1 + sz
  let nm := (t[pos]!).toNat
  pos := pos + 1
  let mut ms : Array (Nat × List (Nat × Nat × Nat)) := #[]
  for _ in [0:nm] do
    let rep := (t[pos]!).toNat
    let cnt := (t[pos + 1]!).toNat
    let ins := (List.range cnt).map fun k =>
      ((t[pos + 2 + 3 * k]!).toNat, (t[pos + 3 + 3 * k]!).toNat, (t[pos + 4 + 3 * k]!).toNat)
    ms := ms.push (rep, ins)
    pos := pos + 2 + 3 * cnt
  return (orbs.toList, ms.toList)

end CFSG.Sporadic.Schreier.PairText
