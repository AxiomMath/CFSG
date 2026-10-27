module

public import Certificates.Data.CFSGNative.Co1.Odd

public section

namespace CFSG.Sporadic.Co1.OddCentNative

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative

structure VTree where
  pts : Array Nat
  par : Array Nat
  lab : Array Nat
deriving Inhabited

@[expose] def vtreePointOK (Gt : Array (Array Nat)) (root : Nat) (T : VTree) (i : Nat) : Bool :=
  decide (T.pts[i]! < 16777216) &&
    (if i == 0 then T.pts[i]! == root
     else decide (T.par[i]! < i) && decide (T.lab[i]! < Gt.size) &&
       T.pts[i]! == vecMulN 24 Gt[T.lab[i]!]! T.pts[T.par[i]!]!)

@[expose] def vtreeOK (Gr : Array (Array Nat)) (root : Nat) (T : VTree) : Bool :=
  decide (0 < T.pts.size) && T.par.size == T.pts.size && T.lab.size == T.pts.size &&
    (List.range T.pts.size).all (vtreePointOK (Gr.map (transposeRows 24)) root T) &&
    distinctKeys T.pts.toList

def vtreeBFS (Gr : Array (Array Nat)) (root cap : Nat) : VTree :=
  Id.run do
    let Gt := Gr.map (transposeRows 24)
    let mut pts : Array Nat := #[root]
    let mut par : Array Nat := #[0]
    let mut lab : Array Nat := #[0]
    let mut seen : Std.HashSet Nat := ({} : Std.HashSet Nat).insert root
    let mut h := 0
    while h < pts.size && pts.size < cap do
      for l in [0:Gt.size] do
        let y := vecMulN 24 Gt[l]! pts[h]!
        if !seen.contains y then
          seen := seen.insert y
          pts := pts.push y
          par := par.push h
          lab := lab.push l
      h := h + 1
    return ⟨pts, par, lab⟩

end CFSG.Sporadic.Co1.OddCentNative
