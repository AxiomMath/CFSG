module

public import Mathlib.AlgebraicGeometry.Group.Smooth

/-!
# Reduced group schemes over an algebraically closed field are smooth

This file is adapted from `Mathlib/AlgebraicGeometry/Group/Smooth.lean`
(Copyright (c) 2026 Andrew Yang; released under the Apache 2.0 license), where the statement
below is the private lemma `AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed`. Mathlib only
exports the geometrically reduced version, so the argument is reproduced here.

Let `G` be a reduced group scheme locally of finite type over an algebraically closed field `K`.
Then `G` is a Jacobson space with a closed point (the identity). The smooth locus is open and
dense (`Scheme.Hom.dense_smoothLocus_of_perfectField`), so it contains a closed point `y`. If a
closed point `x` were outside the smooth locus, right translation by `x⁻¹ y`, an automorphism of
`G` over `Spec K`, would carry `x` to `y` and preserve the smooth locus; hence the non-smooth
locus has no closed points and is empty (`smooth_of_grpObj_of_isReduced_of_isAlgClosed`).
-/

public section

open CategoryTheory

namespace CFSG.ThirdParty.Mathlib

open AlgebraicGeometry MonObj MonoidalCategory CartesianMonoidalCategory

universe u

variable {K : Type u} [Field K] {G : Scheme.{u}} (f : G ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [GrpObj (Over.mk f)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A reduced group scheme locally of finite type over an algebraically closed field `K` is
smooth over `K`. -/
theorem smooth_of_grpObj_of_isReduced_of_isAlgClosed [IsReduced G] [IsAlgClosed K] :
    Smooth f := by
  have := LocallyOfFiniteType.jacobsonSpace f
  have : Nonempty G := ⟨η[Over.mk f].1 (IsLocalRing.closedPoint _)⟩
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro H
  obtain ⟨x, hx, hxc⟩ :=
    nonempty_inter_closedPoints H f.smoothLocus.2.isClosed_compl.isLocallyClosed
  obtain ⟨y, hy : y ∈ f.smoothLocus, hyc⟩ := nonempty_inter_closedPoints
    f.dense_smoothLocus_of_perfectField.nonempty f.smoothLocus.2.isLocallyClosed
  let x' : 𝟙_ _ ⟶ Over.mk f := Over.homMk _ ((pointEquivClosedPoint f).symm ⟨x, hxc⟩).2
  let y' : 𝟙_ _ ⟶ Over.mk f := Over.homMk _ ((pointEquivClosedPoint f).symm ⟨y, hyc⟩).2
  let α := (GrpObj.mulRight (A := Over.mk f) x').symm ≪≫
    (GrpObj.mulRight (A := Over.mk f) y')
  have hα : x' ≫ α.hom = y' := by
    dsimp only [Iso.trans_hom, Iso.symm_hom, α]
    rw [← Category.assoc, ← Iso.eq_comp_inv]
    simp [comp_lift_assoc]
  have hα' : α.hom.left x = y := by
    simpa [x', y', pointEquivClosedPoint] using congr(($hα).left (IsLocalRing.closedPoint K))
  rw! [← hα', ← α.hom.left.mem_preimage, Scheme.Hom.preimage_smoothLocus_eq,
    show α.hom.left ≫ f = f from α.hom.w] at hy
  exact hx hy

end CFSG.ThirdParty.Mathlib
