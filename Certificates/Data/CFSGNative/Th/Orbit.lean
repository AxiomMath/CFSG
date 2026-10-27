module

public import Certificates.Data.CFSGNative.Th.Core

public section

namespace CFSG.Sporadic.Th.Native

@[inline, expose] def allIn (lo hi : Nat) (p : Nat → Bool) : Bool :=
  Nat.all (hi - lo) fun k _ => p (lo + k)

@[inline, expose] def allStep (j c n : Nat) (p : Nat → Bool) : Bool :=
  Nat.all ((n + c - 1 - j) / c) fun k _ => p (j + c * k)

@[expose] def parAll (n chunks : Nat) (p : Nat → Bool) : Bool :=
  let c := chunks + 1
  ((List.range c).map fun j => Task.spawn fun _ => allStep j c n p).all Task.get

structure BFSState where
  keys : ByteArray
  slots : ByteArray
  alpha : ByteArray
  beta : ByteArray
  par : ByteArray
  count : Nat

@[expose] def slotBits (_ : Unit := ()) : Nat := 28

@[expose] def findSlot (keys slots : ByteArray) (k : Key) : Nat × Nat := Id.run do
  let mask := (1 <<< slotBits) - 1
  let mut h := k.hash.toNat &&& mask
  for _ in [0:(1 <<< slotBits)] do
    let e := readU32 slots h
    if e == 0 then return (h, 0)
    if (readKey keys (e - 1)).beq k then return (h, e)
    h := (h + 1) &&& mask
  return (h, 0)

@[inline, expose] def findInsert (st : BFSState) (k : Key) (parent lab : Nat) : BFSState × Nat :=
  let (h, e) := findSlot st.keys st.slots k
  if e != 0 then (st, e - 1) else
    let i := st.count
    (BFSState.mk (pushKey st.keys k) (writeU32 st.slots h (i + 1)) st.alpha st.beta
       (pushU32 st.par (parent ||| (lab <<< 30))) (i + 1), i)

@[expose] def bfs (tA tB : Array V4) (w : Key) (cap : Nat) : BFSState := Id.run do
  let st0 : BFSState := BFSState.mk (ByteArray.emptyWithCapacity (62 * cap))
    (zeroBytes (4 * (1 <<< slotBits))) (ByteArray.emptyWithCapacity (4 * cap))
    (ByteArray.emptyWithCapacity (4 * cap)) (ByteArray.emptyWithCapacity (4 * cap)) 0
  let (st, _) := findInsert st0 w 0 0
  let mut st := st
  for i in [0:cap] do
    if i < st.count then
      let k := readKey st.keys i
      let (st1, ja) := findInsert st (imageKey tA k) i 1
      let (st2, jb) := findInsert st1 (imageKey tB k) i 2
      st := BFSState.mk st2.keys st2.slots (pushU32 st2.alpha ja) (pushU32 st2.beta jb) st2.par
        st2.count
    else
      break
  return st

@[inline, expose] def treePar (pl : Nat) : Nat := pl &&& 0x3FFFFFFF

@[inline, expose] def treeLab (pl : Nat) : Nat := pl >>> 30

@[inline, expose] def orbitCheckAt (tA tB : Array V4) (st : BFSState) (i : Nat) : Bool :=
  let n := st.count
  let k := readKey st.keys i
  let a := readU32 st.alpha i
  let b := readU32 st.beta i
  k.isCanonical && (findSlot st.keys st.slots k).2 == i + 1 && a < n && b < n &&
    (readKey st.keys a).beq (imageKey tA k) && (readKey st.keys b).beq (imageKey tB k) &&
    (i == 0 ||
      (let pl := readU32 st.par i
       let p := treePar pl
       let l := treeLab pl
       p < i && ((l == 1 && readU32 st.alpha p == i) || (l == 2 && readU32 st.beta p == i))))

@[expose] def orbitOK (tA tB : Array V4) (w : Key) (st : BFSState) (chunks : Nat) : Bool :=
  0 < st.count && st.count < 2 ^ 30 && (readKey st.keys 0).beq w &&
    parAll st.count chunks (orbitCheckAt tA tB st)

end CFSG.Sporadic.Th.Native
