module

public import Certificates.Data.CFSGNative.Th.Core
public import Certificates.Data.CFSGNative.Th.Tables
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.J3.Native

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

@[expose] def orbitSorted (d : Nat) (cA cB : Array Nat) (v0 cap : Nat) : Array Nat := Id.run do
  let mut seen : Std.HashMap Nat Unit := Std.HashMap.emptyWithCapacity (2 * cap)
  seen := seen.insert v0 ()
  let mut pts : Array Nat := #[v0]
  for h in [0:cap] do
    if h < pts.size then
      let v := pts[h]!
      let w := vecMulN d cA v
      if !seen.contains w then
        seen := seen.insert w ()
        pts := pts.push w
      let u := vecMulN d cB v
      if !seen.contains u then
        seen := seen.insert u ()
        pts := pts.push u
    else break
  return pts.qsort (· < ·)

@[expose] def posMap (pts : Array Nat) : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := Std.HashMap.emptyWithCapacity (2 * pts.size)
  for i in [0:pts.size] do
    m := m.insert pts[i]! i
  return m

@[expose] def imageTable (d : Nat) (pm : Std.HashMap Nat Nat) (pts : Array Nat) (c : Array Nat) :
    Table :=
  pts.map fun v => UInt32.ofNat ((pm.get? (vecMulN d c v)).getD 0)

@[expose] def orbitOK (d n : Nat) (cA cB pts : Array Nat) (tA tB : Table) : Bool :=
  pts.size == n &&
    allIn 0 n (fun i => decide (pts[i]! < 2 ^ d) &&
      decide (ap tA i < n) && pts[ap tA i]! == vecMulN d cA pts[i]! &&
      decide (ap tB i < n) && pts[ap tB i]! == vecMulN d cB pts[i]!) &&
    allIn 0 (n - 1) (fun i => decide (pts[i]! < pts[i + 1]!))

end CFSG.Sporadic.J3.Native
