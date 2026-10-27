module

public import Certificates.Data.CFSGNative.J4.Tables
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.J4.Native

open CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def apLoop (t : ByteArray) (q : Array Nat) (k : Nat) : Array Nat :=
  if h : k < q.size then apLoop t (q.set k (rdU32 t q[k]) h) (k + 1) else q
termination_by q.size - k

@[inline, expose] def apTab (t : ByteArray) (q : Array Nat) : Array Nat := apLoop t q 0

@[expose] def fwd (par : ByteArray) (l1 l2 l3 : ByteArray) : Nat → Nat → Array Nat → Array Nat
  | 0, _, q => q
  | f + 1, j, q =>
    if j == 0 then q else
      let r := rdU32 par j
      apTab (letter3 l1 l2 l3 (r >>> 30)) (fwd par l1 l2 l3 f (r &&& 0x3FFFFFFF) q)

@[expose] def bwd (par : ByteArray) (i1 i2 i3 : ByteArray) : Nat → Nat → Array Nat → Array Nat
  | 0, _, q => q
  | f + 1, j, q =>
    if j == 0 then q else
      let r := rdU32 par j
      bwd par i1 i2 i3 f (r &&& 0x3FFFFFFF) (apTab (letter3 i1 i2 i3 (r >>> 30)) q)

@[inline, expose] def pairIdx (l1 l2 : Nat) : Nat :=
  if l1 = 1 then (if l2 = 2 then 0 else if l2 = 3 then 1 else 6)
  else if l1 = 2 then (if l2 = 1 then 2 else if l2 = 2 then 3 else 6)
  else if l1 = 3 then (if l2 = 1 then 4 else if l2 = 3 then 5 else 6)
  else 6

@[expose] def pairLetters (_ : Unit := ()) : Array (Nat × Nat) := #[(1, 2), (1, 3), (2, 1), (2, 2), (3, 1), (3, 3)]

@[expose] def bwd2 (par : ByteArray) (i1 i2 i3 : ByteArray) (pairs : Array ByteArray) :
    Nat → Nat → Array Nat → Array Nat
  | 0, _, q => q
  | f + 1, j, q =>
    if j == 0 then q else
      let r := rdU32 par j
      let l1 := r >>> 30
      let p := r &&& 0x3FFFFFFF
      if p == 0 then apTab (letter3 i1 i2 i3 l1) q else
        let r2 := rdU32 par p
        let k := pairIdx l1 (r2 >>> 30)
        if k < 6 then bwd2 par i1 i2 i3 pairs f (r2 &&& 0x3FFFFFFF) (apTab (pairs[k]?.getD .empty) q)
        else bwd2 par i1 i2 i3 pairs f p (apTab (letter3 i1 i2 i3 l1) q)

structure Level where
  map : NatMap
  par : Array Nat
  lab : Array Nat
  tabs : Array ByteArray
deriving Inhabited

@[expose] def climb (L : Level) : Nat → Nat → Array Nat → Array Nat
  | 0, _, q => q
  | f + 1, k, q =>
    if k == 0 then q else
      climb L f (L.par[k]?.getD 0) (apTab (L.tabs[min (L.lab[k]?.getD 0) 2]?.getD .empty) q)

structure GData where
  n : Nat
  ta : ByteArray
  tb : ByteArray
  tbi : ByteArray
  par : ByteArray
  dep : ByteArray
  q0 : Array Nat
  lev : Level
  slot : Nat
  last : Array (Array Nat)
  lastMap : Std.HashMap (Array Nat) Nat
  cacheDepth : Nat
  cacheMap : NatMap
  cache : Array (Array Nat)
  pairs : Array ByteArray
deriving Inhabited

@[expose] def fwdC (G : GData) : Nat → Nat → Array Nat
  | 0, _ => G.q0
  | f + 1, j =>
    if j == 0 then G.q0 else
    if depOf G.dep j == G.cacheDepth then
      let s := G.cacheMap.find j
      if s < G.cacheMap.keys.size && G.cacheMap.keys[s]! == j && s < G.cache.size then G.cache[s]!
      else fwd G.par G.ta G.tb G.tbi 64 j G.q0
    else
      let r := rdU32 G.par j
      apTab (letter3 G.ta G.tb G.tbi (r >>> 30)) (fwdC G f (r &&& 0x3FFFFFFF))

@[expose] def mkCache (par ta tb tbi : ByteArray) (q0 : Array Nat) (pts : Array Nat) :
    Array (Array Nat) :=
  pts.map fun a => fwd par ta tb tbi 64 a q0

@[expose] def globalTest (G : GData) (x : Array Nat) (s i : Nat) : Bool :=
  let st := if s = 1 then G.ta else G.tb
  let z := bwd2 G.par G.ta G.tbi G.tb G.pairs 64 (rdU32 st i) (apTab st x)
  let k := G.lev.map.find (z[G.slot]?.getD 0)
  if k < G.lev.map.keys.size then
    let z := climb G.lev 64 k z
    match G.lastMap.get? z with
    | some e => G.last[e]?.getD #[] == z
    | none => false
  else false

@[inline, expose] def treeEdge (par : ByteArray) (l i j : Nat) : Bool :=
  j != 0 && parOf par j == i && labOf par j == l

@[inline, expose] def reqA (G : GData) (i : Nat) : Bool :=
  let j := rdU32 G.ta i
  !treeEdge G.par 1 i j && !treeEdge G.par 1 j i && (j == i || j < i)

@[inline, expose] def trivB (G : GData) (i : Nat) : Bool :=
  let j := rdU32 G.tb i
  treeEdge G.par 2 i j || treeEdge G.par 3 j i

@[inline, expose] def reqB (G : GData) (i : Nat) : Bool :=
  let i1 := rdU32 G.tb i
  let i2 := rdU32 G.tb i1
  let i3 := rdU32 G.tb i2
  !trivB G i &&
    (i1 == i || i2 == i ||
      (!trivB G i1 && i1 < i) || (!trivB G i2 && i2 < i) || (!trivB G i3 && i3 < i))

@[expose] def globalAt (G : GData) (i : Nat) : Bool :=
  let ra := reqA G i
  let rb := reqB G i
  if ra || rb then
    let x := fwdC G 64 i
    (!ra || globalTest G x 1 i) && (!rb || globalTest G x 2 i)
  else true

@[expose] def globalOK (G : GData) (chunks : Nat) : Bool := parAllR G.n chunks (globalAt G)

end CFSG.Sporadic.J4.Native
