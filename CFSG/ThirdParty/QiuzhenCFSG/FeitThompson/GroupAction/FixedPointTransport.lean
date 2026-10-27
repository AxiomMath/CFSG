module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section FixedPointTransport

variable {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]

/-- Triviality on a subgroup is equivalent to subgroup containment in fixed points. -/
public theorem CFSG.actsTriviallyOnSubgroup_iff_le_fixedPointSubgroup (H : Subgroup G) :
    ActsTriviallyOnSubgroup (A := A) (G := G) H ↔ H ≤ fixedPointSubgroup A G := by
  constructor
  · intro htriv x hx
    change ∀ a : A, a • x = x
    intro a
    exact htriv a x hx
  · intro hle a x hx
    have hxfix : x ∈ fixedPointSubgroup A G := hle hx
    have hxfix' : ∀ b : A, b • x = x := by
      simpa [fixedPointSubgroup] using hxfix
    exact hxfix' a

/-- A subgroup contained in fixed points is fixed pointwise. -/
public theorem CFSG.actsTriviallyOnSubgroup_of_le_fixedPointSubgroup {H : Subgroup G}
    (hle : H ≤ fixedPointSubgroup A G) :
    ActsTriviallyOnSubgroup (A := A) (G := G) H :=
  (actsTriviallyOnSubgroup_iff_le_fixedPointSubgroup (A := A) (G := G) H).2 hle


end FixedPointTransport
