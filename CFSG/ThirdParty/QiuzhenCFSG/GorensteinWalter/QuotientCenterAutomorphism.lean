module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentData

namespace CFSG
end CFSG
open CFSG

/-!
# Automorphisms on a central quotient

An automorphism preserves the center, so it induces an automorphism of the
quotient by the center.  This small interface is used by the Section-4
component action and is kept independent of the particular component model.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The center is carried to itself by every group automorphism. -/
private theorem map_center_eq_center_of_mulAut
    {H : Type u} [Group H] (a : MulAut H) :
    (Subgroup.center H).map a.toMonoidHom = Subgroup.center H := by
  exact map_center_eq_center_of_mulEquiv a

/-- The automorphism induced on the quotient by the center. -/
public def quotientCenterAutomorphism
    (H : Type u) [Group H] :
    MulAut H →* MulAut (H ⧸ Subgroup.center H) where
  toFun a := QuotientGroup.congr (Subgroup.center H) (Subgroup.center H)
    a (map_center_eq_center_of_mulAut a)
  map_one' := by
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    simp [QuotientGroup.congr]
  map_mul' := by
    intro a b
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    simp [QuotientGroup.congr]

@[simp]
public theorem quotientCenterAutomorphism_apply_mk
    {H : Type u} [Group H] (a : MulAut H) (x : H) :
    quotientCenterAutomorphism H a
      (QuotientGroup.mk' (Subgroup.center H) x) =
      QuotientGroup.mk' (Subgroup.center H) (a x) := by
  rfl

end CFSG.GorensteinWalter
