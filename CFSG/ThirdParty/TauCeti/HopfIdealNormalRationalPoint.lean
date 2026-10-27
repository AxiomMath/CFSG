/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
public import TauCeti.RingTheory.FiniteType.PointSeparation
public import TauCeti.RingTheory.FiniteType.Tensor.Product
public import Mathlib.RingTheory.FiniteStability
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Normality of reduced closed subgroups from rational points

This file is adapted from the TauCeti repository:

* `TauCeti/Algebra/AlgebraicGroup/HopfIdeal/Normal/RationalPoint.lean`, at TauCeti `main`
  commit `f3825ea4a4d2c7b7030c4a885dca8785b4bc73a0`, which contains
  `isNormal_of_forall_le_conjugate`, `isNormal_iff_forall_le_conjugate` and
  `IsNormal.comapOfSurjective_of_forall_iso`;
* `TauCeti/Algebra/AlgebraicGroup/HopfIdeal/Conjugation.lean`, at TauCeti `main`
  commit `3edb527dbf3007ec567f305c5543c669ba9a1988`, which contains
  `IsNormal.le_conjugate`.

Copyright (c) 2026 The Tau Ceti contributors; released under the Apache 2.0 license
(https://www.apache.org/licenses/LICENSE-2.0).

The current CFSG dependency pin (`6e0c6acab`) predates these declarations. They are reproduced
in the `CFSG.ThirdParty.TauCeti` namespace so that a later TauCeti bump does not clash with the
upstream names. The statements are unchanged. The proofs are ported verbatim except for the
following adaptations to the pinned API:

* `Ideal.rightTensorIdeal (R := R) (A := H)` is written
  `TauCeti.HopfIdeal.rightTensorIdeal (R := R) (H := H)`, and similarly for
  `rightTensorIdeal_le_iff` and `ker_tensorProduct_map_id_quotient`;
* `TauCeti.HopfIdeal.conjugate_eq_comapOfSurjective` replaces unfolding the `conjugate`
  definition, which is not exposed at the pin;
* the three declarations are placed in namespaces rooted at `CFSG.ThirdParty.TauCeti`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §1.d and §3.5.
-/

public section

open WithConv
open scoped TensorProduct
open CategoryTheory

namespace CFSG.ThirdParty.TauCeti

universe u

namespace HopfIdeal

/-- Every rational point normalizes a normal closed subgroup: conjugation by it maps the defining
ideal into itself. Ported from TauCeti `main`,
`TauCeti/Algebra/AlgebraicGroup/HopfIdeal/Conjugation.lean`. -/
theorem IsNormal.le_conjugate {R : Type u} [CommRing R] {H : Type u} [CommRing H]
    [HopfAlgebra R H] {I : TauCeti.HopfIdeal R H}
    (hI : TauCeti.HopfIdeal.IsNormal I)
    (g : WithConv (H →ₐ[R] R)) : I ≤ I.conjugate g := by
  let f := Algebra.TensorProduct.productMap
    (TauCeti.AlgHom.mapValue (H := H) (Algebra.ofId R H) g).ofConv (AlgHom.id R H)
  have hconj : TauCeti.HopfAlgebra.pointConjugationAlgHom g =
      f.comp (TauCeti.HopfAlgebra.conjugationAlgHom (R := R) (H := H)) := by
    apply WithConv.toConv_injective
    rw [TauCeti.HopfAlgebra.toConv_pointConjugationAlgHom,
      TauCeti.HopfAlgebra.productMap_comp_conjugationAlgHom, WithConv.toConv_ofConv]
  have hker : TauCeti.HopfIdeal.rightTensorIdeal (R := R) (H := H) I.toIdeal ≤
      I.toIdeal.comap f.toRingHom := by
    rw [TauCeti.HopfIdeal.rightTensorIdeal_le_iff]
    intro y hy
    simpa [f] using hy
  intro x hx
  rw [TauCeti.HopfIdeal.mem_conjugate, hconj, AlgHom.comp_apply,
    ← TauCeti.HopfIdeal.mem_toIdeal]
  exact hker ((TauCeti.HopfIdeal.isNormal_iff_conjugation_mem I).mp hI hx)

/-- **Normality from rational points.** Over an algebraically closed field, a reduced closed
subgroup of a reduced finite-type affine group is normal when conjugation by every rational
point maps it into itself. Ported from TauCeti `main`,
`TauCeti/Algebra/AlgebraicGroup/HopfIdeal/Normal/RationalPoint.lean`. -/
theorem isNormal_of_forall_le_conjugate {k : Type u} [Field k] [IsAlgClosed k]
    {H : Type u} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] [IsReduced H]
    (I : TauCeti.HopfIdeal k H) [IsReduced (H ⧸ I.toIdeal)]
    (hI : ∀ g : WithConv (H →ₐ[k] k), I ≤ I.conjugate g) :
    TauCeti.HopfIdeal.IsNormal I := by
  rw [TauCeti.HopfIdeal.isNormal_iff_conjugation_mem]
  intro x hx
  let q : H →ₐ[k] H ⧸ I.toIdeal := Ideal.Quotient.mkₐ k I.toIdeal
  let F : H ⊗[k] H →ₐ[k] H ⊗[k] (H ⧸ I.toIdeal) :=
    Algebra.TensorProduct.map (AlgHom.id k H) q
  let _ : Algebra.FiniteType k (H ⊗[k] (H ⧸ I.toIdeal)) :=
    Algebra.FiniteType.trans (R := k) (S := H) (A := H ⊗[k] (H ⧸ I.toIdeal))
      inferInstance inferInstance
  rw [← TauCeti.HopfIdeal.ker_tensorProduct_map_id_quotient, RingHom.mem_ker]
  apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k)
  intro φ
  let g : WithConv (H →ₐ[k] k) :=
    WithConv.toConv ((φ.comp F).comp Algebra.TensorProduct.includeLeft)
  let h : WithConv (H →ₐ[k] k) :=
    WithConv.toConv ((φ.comp F).comp Algebra.TensorProduct.includeRight)
  have hh : ∀ y ∈ I, h.ofConv y = 0 := by
    intro y hy
    simp [h, F, q, Ideal.Quotient.eq_zero_iff_mem.mpr
      (TauCeti.HopfIdeal.mem_toIdeal.mpr hy)]
  have hconj := AlgHom.congr_fun (TauCeti.HopfAlgebra.comp_conjugationAlgHom (φ.comp F)) x
  have hpoint := TauCeti.HopfAlgebra.comp_pointConjugationAlgHom g h
  rw [Algebra.ofId_self, TauCeti.AlgHom.mapValue_id, MonoidHom.id_apply] at hpoint
  rw [map_zero]
  calc φ (F (TauCeti.HopfAlgebra.conjugationAlgHom x))
      = (g * h * g⁻¹).ofConv x := hconj
    _ = h.ofConv (TauCeti.HopfAlgebra.pointConjugationAlgHom g x) := by
      rw [← hpoint, WithConv.ofConv_toConv, AlgHom.comp_apply]
    _ = 0 := hh _ (TauCeti.HopfIdeal.mem_conjugate.mp (hI g hx))

/-- A reduced characteristic closed subgroup of a normal closed subgroup is normal in the
ambient reduced finite-type affine group over an algebraically closed field. Ported from
TauCeti `main`, `TauCeti/Algebra/AlgebraicGroup/HopfIdeal/Normal/RationalPoint.lean`. -/
theorem IsNormal.comapOfSurjective_of_forall_iso {k : Type u} [Field k] [IsAlgClosed k]
    {H : Type u} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] [IsReduced H]
    {I : TauCeti.HopfIdeal k H} (hI : TauCeti.HopfIdeal.IsNormal I)
    (J : TauCeti.HopfIdeal k
      (TauCeti.CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I))
    [IsReduced (H ⧸ (J.comapOfSurjective
      (TauCeti.CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) I).hom
      (TauCeti.CommHopfAlgCat.mkQuotient_surjective _ _)).toIdeal)]
    (hJ : ∀ e : TauCeti.CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I ≅
        TauCeti.CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I,
      J.comapOfSurjective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2 = J) :
    TauCeti.HopfIdeal.IsNormal
      (J.comapOfSurjective
        (TauCeti.CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) I).hom
        (TauCeti.CommHopfAlgCat.mkQuotient_surjective _ _)) := by
  apply isNormal_of_forall_le_conjugate
  intro g x hx
  let A := _root_.CommHopfAlgCat.of k H
  let c : A ≅ A := _root_.CommHopfAlgCat.isoMk
    (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g)
  have hstable : I.comapOfSurjective c.hom.hom
      (ConcreteCategory.bijective_of_isIso c.hom).2 = I := by
    have hconj : I.conjugate g = I := by
      apply le_antisymm
      · have h : (I.conjugate g⁻¹).conjugate g = I := by
          rw [← TauCeti.HopfIdeal.conjugate_mul, mul_inv_cancel,
            TauCeti.HopfIdeal.conjugate_one]
        simpa [h] using TauCeti.HopfIdeal.conjugate_mono g
          (IsNormal.le_conjugate hI g⁻¹)
      · exact IsNormal.le_conjugate hI g
    simpa only [TauCeti.HopfIdeal.conjugate_eq_comapOfSurjective, c,
      _root_.CommHopfAlgCat.isoMk_hom, _root_.CommHopfAlgCat.hom_ofHom,
      BialgEquiv.toBialgHom_eq_coe] using hconj
  let e := TauCeti.CommHopfAlgCat.quotientIsoOfComapEq c I hstable
  have hcomm :=
    TauCeti.CommHopfAlgCat.mkQuotient_comp_quotientIsoOfComapEq_hom c I hstable
  have heval := congrArg (fun f : A ⟶ TauCeti.CommHopfAlgCat.quotient A I ↦ f.hom x) hcomm
  have hxJ : (TauCeti.CommHopfAlgCat.mkQuotient A I).hom x ∈ J :=
    TauCeti.HopfIdeal.mem_comapOfSurjective.mp hx
  have hpreserved : e.hom.hom ((TauCeti.CommHopfAlgCat.mkQuotient A I).hom x) ∈ J :=
    TauCeti.HopfIdeal.mem_comapOfSurjective.mp ((hJ e).symm ▸ hxJ)
  rw [TauCeti.HopfIdeal.mem_conjugate, TauCeti.HopfIdeal.mem_comapOfSurjective]
  simp only [_root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply] at heval
  rw [heval] at hpreserved
  simpa only [c, _root_.CommHopfAlgCat.isoMk_hom, _root_.CommHopfAlgCat.hom_ofHom,
    BialgHom.coe_coe, BialgHom.coe_toAlgHom, BialgEquiv.coe_coe,
    ← TauCeti.HopfAlgebra.pointConjugationBialgEquiv_toAlgHom] using hpreserved

end HopfIdeal

end CFSG.ThirdParty.TauCeti
