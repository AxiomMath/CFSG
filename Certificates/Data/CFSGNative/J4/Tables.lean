module

public import Certificates.Data.CFSGNative.J4.Orbit

public section

namespace CFSG.Sporadic.J4.Native

open CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def matTab (keys slots : ByteArray) (n : Nat) (tM : Array V2) (chunks : Nat) :
    ByteArray :=
  tabulatePar n chunks fun i => findIdx keys slots (frApply tM (rdV2 keys i)) - 1

@[expose] def matTabOK (keys : ByteArray) (n : Nat) (tM : Array V2) (t : ByteArray) (chunks : Nat) :
    Bool :=
  parAllS n chunks fun i =>
    let j := rdU32 t i
    j < n && (rdV2 keys j).beq (frApply tM (rdV2 keys i))

structure VOrb where
  pts : Array V2
  par : Array Nat
  lab : Array Nat
  slots : ByteArray
  bits : Nat
deriving Inhabited

@[expose] def vfind (pts : Array V2) (slots : ByteArray) (bits : Nat) (k : V2) : Nat := Id.run do
  let mask := 2 ^ bits - 1
  let mut h := k.hash.toNat &&& mask
  for _ in [0:2 ^ bits] do
    let e := rdU32 slots h
    if e == 0 then return 0
    if (pts[e - 1]?.getD V2.zero).beq k then return e
    h := (h + 1) &&& mask
  return 0

@[expose] def vslot (slots : ByteArray) (bits : Nat) (k : V2) : Nat := Id.run do
  let mask := 2 ^ bits - 1
  let mut h := k.hash.toNat &&& mask
  for _ in [0:2 ^ bits] do
    if rdU32 slots h == 0 then return h
    h := (h + 1) &&& mask
  return h

@[inline, expose] def vinsert (pts : Array V2) (slots : ByteArray) (bits : Nat) (k : V2) :
    ByteArray :=
  wrU32 slots (vslot slots bits k) (pts.size + 1)

@[expose] def vorbit (ts : Array (Array V2)) (w : V2) (cap bits : Nat) : VOrb := Id.run do
  let mut pts : Array V2 := Array.mkEmpty cap
  let mut par : Array Nat := Array.mkEmpty cap
  let mut lab : Array Nat := Array.mkEmpty cap
  let mut slots := zeros (4 * 2 ^ bits)
  slots := vinsert pts slots bits w
  pts := pts.push w
  par := par.push 0
  lab := lab.push 0
  for q in [0:cap] do
    if q < pts.size then
      let p := pts[q]!
      for g in [0:ts.size] do
        let y := frApply ts[g]! p
        if vfind pts slots bits y == 0 && pts.size < cap then
          slots := vinsert pts slots bits y
          pts := pts.push y
          par := par.push q
          lab := lab.push g
    else break
  return ⟨pts, par, lab, slots, bits⟩

@[inline, expose] def vorbAt (ts : Array (Array V2)) (O : VOrb) (q : Nat) : Bool :=
  let p := O.pts[q]!
  p.wf && vfind O.pts O.slots O.bits p == q + 1 &&
    (List.range ts.size).all (fun g =>
      let e := vfind O.pts O.slots O.bits (frApply ts[g]! p)
      e != 0 && e ≤ O.pts.size && (O.pts[e - 1]!).beq (frApply ts[g]! p)) &&
    (q == 0 || (O.par[q]! < q && O.lab[q]! < ts.size &&
      (frApply ts[O.lab[q]!]! O.pts[O.par[q]!]!).beq p))

@[expose] def vorbOK (ts : Array (Array V2)) (w : V2) (O : VOrb) (m : Nat) : Bool :=
  O.pts.size == m && O.par.size == m && O.lab.size == m && 0 < m && (O.pts[0]!).beq w &&
    (List.range m).all (vorbAt ts O)

structure NatMap where
  keys : Array Nat
  slots : ByteArray
  bits : Nat
deriving Inhabited

@[expose] def NatMap.find (M : NatMap) (k : Nat) : Nat := Id.run do
  let mask := 2 ^ M.bits - 1
  let mut h := (mix (UInt64.ofNat k)).toNat &&& mask
  for _ in [0:2 ^ M.bits] do
    let e := rdU32 M.slots h
    if e == 0 then return M.keys.size
    if M.keys[e - 1]! == k then return e - 1
    h := (h + 1) &&& mask
  return M.keys.size

@[expose] def NatMap.slotsOf (keys : Array Nat) (bits : Nat) : ByteArray := Id.run do
  let mask := 2 ^ bits - 1
  let mut slots := zeros (4 * 2 ^ bits)
  for i in [0:keys.size] do
    let mut h := (mix (UInt64.ofNat keys[i]!)).toNat &&& mask
    for _ in [0:2 ^ bits] do
      if rdU32 slots h == 0 then
        slots := wrU32 slots h (i + 1)
        break
      h := (h + 1) &&& mask
  return slots

@[expose] def NatMap.ofKeys (keys : Array Nat) (bits : Nat) : NatMap :=
  ⟨keys, NatMap.slotsOf keys bits, bits⟩

end CFSG.Sporadic.J4.Native
