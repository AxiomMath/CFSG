module

public import Certificates.Data.CFSGNative.Co1Schreier.Base
public import Std.Data.HashSet.Basic

public section

namespace CFSG.Sporadic.Co1Schreier.Native

open CFSG.Sporadic.SmallF2.Native

@[expose] def vBfs (cols : Array Rows) (gens : List Nat) (root bound : Nat) :
    Array (Nat × Nat × Nat) :=
  Id.run do
    let mut seen : Std.HashSet Nat := (Std.HashSet.emptyWithCapacity 10000).insert root
    let mut out : Array (Nat × Nat × Nat) := #[(root, 0, 0)]
    for i in [0:bound] do
      if h : i < out.size then
        let v := out[i].1
        for g in gens do
          let w := vecMulN 24 (cols.getD g #[]) v
          if !seen.contains w then
            seen := seen.insert w
            out := out.push (w, i, g)
    return out

@[expose] def vSorted : List Nat → Bool
  | a :: b :: r => decide (a < b) && vSorted (b :: r)
  | _ => true

@[expose] def vTreeOK (cols : Array Rows) (gens : List Nat) (root n : Nat)
    (t : Array (Nat × Nat × Nat)) : Bool :=
  t.size == n && (t.getD 0 (0, 0, 0)).1 == root &&
    (List.range n).all (fun m => decide ((t.getD m (0, 0, 0)).1 < 2 ^ 24) &&
      (m == 0 || (decide ((t.getD m (0, 0, 0)).2.1 < m) && gens.contains (t.getD m (0, 0, 0)).2.2 &&
        (t.getD m (0, 0, 0)).1 == vecMulN 24 (cols.getD (t.getD m (0, 0, 0)).2.2 #[])
          (t.getD (t.getD m (0, 0, 0)).2.1 (0, 0, 0)).1))) &&
    vSorted ((t.toList.map (·.1)).mergeSort fun a b => decide (a ≤ b))

@[expose] def vTowerOK (cols : Array Rows) (base : List Nat) (gens : List (List Nat))
    (sizes : List Nat) : Bool :=
  (List.range base.length).all fun i =>
    decide (base.getD i 0 < 2 ^ 24) &&
      (gens.getD i []).all (fun j => decide (j < cols.size) &&
        (List.range i).all fun l =>
          vecMulN 24 (cols.getD j #[]) (base.getD l 0) == base.getD l 0) &&
      vTreeOK cols (gens.getD i []) (base.getD i 0) (sizes.getD i 0)
        (vBfs cols (gens.getD i []) (base.getD i 0) (sizes.getD i 0))

end CFSG.Sporadic.Co1Schreier.Native
