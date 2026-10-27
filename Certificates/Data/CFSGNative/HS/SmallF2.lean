module

public import Certificates.Data.CFSGNative.Th.Core
public import Certificates.Data.CFSGNative.Th.Tables

public section

namespace CFSG.Sporadic.SmallF2.Native

open CFSG.Sporadic.Th.Native

@[expose] def vecMulN (d : Nat) (R : Array Nat) (v : Nat) : Nat :=
  (List.range d).foldl (fun acc j => if v.testBit j then acc ^^^ (R[j]?.getD 0) else acc) 0

@[expose] def mulRows (d : Nat) (X Y : Array Nat) : Array Nat := X.map (vecMulN d Y)

@[expose] def ofBits (d : Nat) (f : Nat → Bool) : Nat :=
  (List.range d).foldl (fun acc j => if f j then acc ||| (1 <<< j) else acc) 0

@[expose] def transposeRows (d : Nat) (R : Array Nat) : Array Nat :=
  Array.ofFn (n := d) fun j => ofBits d fun i => (R[i]?.getD 0).testBit j.val

@[expose] def idRows (d : Nat) : Array Nat := Array.ofFn (n := d) fun i => 1 <<< i.val

@[expose] def powRows (d : Nat) (M : Array Nat) : Nat → Array Nat
  | 0 => idRows d
  | e + 1 => mulRows d (powRows d M e) M

@[expose] def rowsOfPayload (d : Nat) (s : String) : Array Nat :=
  let e := (decodeEntries s).toArray
  Array.ofFn (n := d) fun i => ofBits d fun j => (e[i.val * d + j]?.getD 0) % 2 == 1

structure VOrbit where
  pts : Array Nat
  alpha : Table
  beta : Table
deriving Inhabited

@[expose] def vOrbitBFS (d : Nat) (cA cB : Array Nat) (v0 cap : Nat) : VOrbit := Id.run do
  let mut pos : Array UInt32 := Array.replicate (1 <<< d) none32
  let mut pts : Array Nat := #[v0]
  pos := pos.set! v0 0
  let mut alpha : Table := #[]
  let mut beta : Table := #[]
  for h in [0:cap] do
    if h < pts.size then
      let v := pts[h]!
      let w := vecMulN d cA v
      if pos[w]! == none32 then
        pos := pos.set! w (UInt32.ofNat pts.size)
        pts := pts.push w
      alpha := alpha.push pos[w]!
      let u := vecMulN d cB v
      if pos[u]! == none32 then
        pos := pos.set! u (UInt32.ofNat pts.size)
        pts := pts.push u
      beta := beta.push pos[u]!
    else break
  return ⟨pts, alpha, beta⟩

@[expose] def posTable (d : Nat) (pts : Array Nat) : Array UInt32 := Id.run do
  let mut pos : Array UInt32 := Array.replicate (1 <<< d) none32
  for i in [0:pts.size] do
    pos := pos.set! pts[i]! (UInt32.ofNat i)
  return pos

@[expose] def vOrbitOK (d n : Nat) (cA cB : Array Nat) (O : VOrbit) : Bool :=
  let pos := posTable d O.pts
  O.pts.size == n && O.alpha.size == n && O.beta.size == n &&
    allIn 0 n fun i => decide (O.pts[i]! < 2 ^ d) && (pos[O.pts[i]!]!).toNat == i &&
      decide (ap O.alpha i < n) && O.pts[ap O.alpha i]! == vecMulN d cA O.pts[i]! &&
      decide (ap O.beta i < n) && O.pts[ap O.beta i]! == vecMulN d cB O.pts[i]!

end CFSG.Sporadic.SmallF2.Native
