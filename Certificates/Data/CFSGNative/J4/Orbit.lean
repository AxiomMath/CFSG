module

public import Certificates.Data.CFSGNative.J4.Store
public import Certificates.Data.CFSGNative.Th.Orbit

public section

namespace CFSG.Sporadic.J4.Native

open CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

structure BFSState where
  keys : ByteArray
  slots : ByteArray
  alpha : ByteArray
  beta : ByteArray
  count : Nat

@[expose] def slotMask (_ : Unit := ()) : Nat := 2 ^ 28 - 1

@[inline, expose] def tagOf (k : V2) : Nat := (k.hash >>> 60).toNat

@[expose] def findSlot (keys slots : ByteArray) (k : V2) : Nat × Nat := Id.run do
  let hk := k.hash
  let tg := (hk >>> 60).toNat
  let mut h := hk.toNat &&& slotMask
  for _ in [0:2 ^ 28] do
    let e := rdU32 slots h
    if e == 0 then return (h, 0)
    let e1 := e &&& slotMask
    if e >>> 28 == tg && (rdV2 keys (e1 - 1)).beq k then return (h, e1)
    h := (h + 1) &&& slotMask
  return (h, 0)

@[inline, expose] def findIdx (keys slots : ByteArray) (k : V2) : Nat := (findSlot keys slots k).2

@[inline, expose] def findInsert (st : BFSState) (k : V2) : BFSState × Nat :=
  let (h, e) := findSlot st.keys st.slots k
  if e != 0 then (st, e - 1) else
    let i := st.count
    (BFSState.mk (pushV2 st.keys k) (wrU32 st.slots h ((i + 1) ||| (tagOf k <<< 28))) st.alpha
      st.beta (i + 1), i)

@[expose] def bfs (tA tB : Array V2) (w : V2) (cap : Nat) : BFSState := Id.run do
  let st0 : BFSState := BFSState.mk (ByteArray.emptyWithCapacity (16 * cap))
    (zeros (4 * 2 ^ 28)) (ByteArray.emptyWithCapacity (4 * cap))
    (ByteArray.emptyWithCapacity (4 * cap)) 0
  let (st, _) := findInsert st0 w
  let mut st := st
  for i in [0:cap] do
    if i < st.count then
      let k := rdV2 st.keys i
      let (st1, ja) := findInsert st (frApply tA k)
      let (st2, jb) := findInsert st1 (frApply tB k)
      st := BFSState.mk st2.keys st2.slots (pushU32 st2.alpha ja) (pushU32 st2.beta jb) st2.count
    else
      break
  return st

@[inline, expose] def orbitCheckAt (tA tB : Array V2) (st : BFSState) (n i : Nat) : Bool :=
  let k := rdV2 st.keys i
  let a := rdU32 st.alpha i
  let b := rdU32 st.beta i
  k.wf && findIdx st.keys st.slots k == i + 1 && a < n && b < n &&
    (rdV2 st.keys a).beq (frApply tA k) && (rdV2 st.keys b).beq (frApply tB k)

@[expose] def orbitOK (tA tB : Array V2) (w : V2) (st : BFSState) (n chunks : Nat) : Bool :=
  0 < n && n < 2 ^ 28 && (rdV2 st.keys 0).beq w && parAllS n chunks (orbitCheckAt tA tB st n)

@[expose] def invTab (n : Nat) (t : ByteArray) (chunks : Nat) : ByteArray :=
  let c := chunks + 1
  let len := (n + c - 1) / c
  let parts := (List.range c).map fun j => Task.spawn fun _ => Id.run do
    let lo := j * len
    let hi := min n (lo + len)
    let mut r := zeros (4 * (hi - lo))
    for i in [0:n] do
      let v := rdU32 t i
      if lo ≤ v && v < hi then r := wrU32 r (v - lo) i
    return r
  parts.foldl (fun acc t => acc ++ t.get) (ByteArray.emptyWithCapacity (4 * n))

@[expose] def compTab (n : Nat) (p q : ByteArray) (chunks : Nat) : ByteArray :=
  tabulatePar n chunks fun i => rdU32 p (rdU32 q i)

@[expose] def compOK (n : Nat) (c p q : ByteArray) (chunks : Nat) : Bool :=
  parAllS n chunks fun i => rdU32 c i == rdU32 p (rdU32 q i)

@[expose] def invOK32 (n : Nat) (t r : ByteArray) (chunks : Nat) : Bool :=
  parAllS n chunks fun i => rdU32 t i < n && rdU32 r (rdU32 t i) == i

@[inline, expose] def letter3 (ta tb tc : ByteArray) (l : Nat) : ByteArray :=
  if l = 1 then ta else if l = 2 then tb else tc

@[expose] def tree2 (n : Nat) (ta tb tc : ByteArray) : ByteArray × ByteArray := Id.run do
  let mut dep : ByteArray := ByteArray.emptyWithCapacity n
  for _ in [0:n] do
    dep := dep.push 255
  let mut par := zeros (4 * n)
  let mut queue := ByteArray.emptyWithCapacity (4 * n)
  dep := dep.set! 0 0
  queue := pushU32 queue 0
  let mut qn := 1
  for h in [0:n] do
    if h < qn then
      let p := rdU32 queue h
      let d := dep.get! p
      for l in [1:4] do
        let q := rdU32 (letter3 ta tb tc l) p
        if dep.get! q == 255 then
          dep := dep.set! q (d + 1)
          par := wrU32 par q (p ||| (l <<< 30))
          queue := pushU32 queue q
          qn := qn + 1
    else break
  return (par, dep)

@[inline, expose] def parOf (par : ByteArray) (j : Nat) : Nat := rdU32 par j &&& 0x3FFFFFFF

@[inline, expose] def labOf (par : ByteArray) (j : Nat) : Nat := rdU32 par j >>> 30

@[inline, expose] def depOf (dep : ByteArray) (j : Nat) : Nat := (dep.get! j).toNat

@[inline, expose] def treeAt (n : Nat) (ta tb tc par dep : ByteArray) (j : Nat) : Bool :=
  depOf dep j < 64 &&
    if j == 0 then depOf dep 0 == 0 else
      let p := parOf par j
      let l := labOf par j
      p < n && 1 ≤ l && l ≤ 3 && rdU32 (letter3 ta tb tc l) p == j &&
        depOf dep p + 1 == depOf dep j

@[expose] def treeOK (n : Nat) (ta tb tc par dep : ByteArray) (chunks : Nat) : Bool :=
  parAllS n chunks (treeAt n ta tb tc par dep)

end CFSG.Sporadic.J4.Native
