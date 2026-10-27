/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import CFSG.ThirdParty.TauCeti.OppositeCocharacter
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Parabolic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
public import TauCeti.Algebra.Polynomial.Laurent.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Representability of the dynamic parabolic, unipotent and Levi subgroups

This file is adapted from the TauCeti repository at `main` commit
`6fee5c0a9fb3444eb4aa6a4a6248c33258a11d5c`. The CFSG dependency pin
`6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380` predates these results. The declarations are
reproduced in the `CFSG.ThirdParty.TauCeti` namespace with unchanged statements, so that a
later TauCeti bump does not clash with the upstream names; references to declarations that
are already at the pin point at those pinned declarations.

The source files and their main declarations are:

* `TauCeti/Algebra/AlgebraicGroup/HopfIdeal/Points/Representability.lean`:
  `CFSG.ThirdParty.TauCeti.HopfIdeal.ofIdealOfPointsSubgroup` and
  `CFSG.ThirdParty.TauCeti.HopfIdeal.ofIdealOfPointsSubgroup_toIdeal`, the pointwise
  criterion for an ideal to be a Hopf ideal;
* `TauCeti/Algebra/AlgebraicGroup/Dynamic/Representability.lean`:
  `CFSG.ThirdParty.TauCeti.Cocharacter.conjugationAlgHom`,
  `CFSG.ThirdParty.TauCeti.Cocharacter.coeff_conjugate`,
  `CFSG.ThirdParty.TauCeti.Cocharacter.coeff_conjugationAlgHom_coeff`,
  `CFSG.ThirdParty.TauCeti.Cocharacter.conjugate_ofConv_coeff_conjugationAlgHom`,
  `CFSG.ThirdParty.TauCeti.Cocharacter.parabolicDefiningHopfIdeal`,
  `CFSG.ThirdParty.TauCeti.Cocharacter.parabolicDefiningHopfIdeal_toIdeal`,
  `CFSG.ThirdParty.TauCeti.Cocharacter.mem_parabolicDefiningHopfIdeal`,
  `CFSG.ThirdParty.TauCeti.Cocharacter.coeff_conjugationAlgHom_mem_parabolicDefiningHopfIdeal`,
  `CFSG.ThirdParty.TauCeti.Cocharacter.quotientPointsSubgroup_parabolicDefiningHopfIdeal`,
  `CFSG.ThirdParty.TauCeti.Cocharacter.parabolicDefiningHopfIdeal_le_iff` and
  `CFSG.ThirdParty.TauCeti.BialgHom.parabolic_eq_top_of_parabolicDefiningHopfIdeal_eq_bot`;
* `TauCeti/Algebra/AlgebraicGroup/Dynamic/Unipotent/Representability.lean`:
  `CFSG.ThirdParty.TauCeti.BialgHom.limit_eq_one_iff_coeff_conjugationAlgHom`,
  `CFSG.ThirdParty.TauCeti.BialgHom.unipotentDefiningHopfIdeal`,
  `CFSG.ThirdParty.TauCeti.BialgHom.unipotentDefiningHopfIdeal_toIdeal`,
  `CFSG.ThirdParty.TauCeti.BialgHom.mem_unipotentDefiningHopfIdeal`,
  `CFSG.ThirdParty.TauCeti.BialgHom.parabolicDefiningHopfIdeal_le_unipotentDefiningHopfIdeal`,
  `CFSG.ThirdParty.TauCeti.BialgHom.`
  `coeff_conjugationAlgHom_sub_counit_mem_unipotentDefiningHopfIdeal`,
  `CFSG.ThirdParty.TauCeti.BialgHom.unipotentDefiningHopfIdeal_le_iff`,
  `CFSG.ThirdParty.TauCeti.BialgHom.quotientPointsSubgroup_unipotentDefiningHopfIdeal` and
  `CFSG.ThirdParty.TauCeti.BialgHom.`
  `isNormal_unipotentDefiningHopfIdeal_of_parabolicDefiningHopfIdeal_eq_bot`;
* `TauCeti/Algebra/AlgebraicGroup/Dynamic/Levi/Representability.lean`:
  `CFSG.ThirdParty.TauCeti.Cocharacter.leviDefiningHopfIdeal`,
  `CFSG.ThirdParty.TauCeti.Cocharacter.leviDefiningHopfIdeal_def`,
  `CFSG.ThirdParty.TauCeti.Cocharacter.leviDefiningHopfIdeal_oppositeCocharacter` and
  `CFSG.ThirdParty.TauCeti.Cocharacter.quotientPointsSubgroup_leviDefiningHopfIdeal`;
* `TauCeti/Algebra/AlgebraicGroup/Dynamic/Parabolic.lean` (new revision):
  `CFSG.ThirdParty.TauCeti.Cocharacter.mapValue_laurentEval_one_conjugate`,
  `CFSG.ThirdParty.TauCeti.Cocharacter.mem_parabolic_iff_forall_coeff_conjugate_eq_zero`,
  `CFSG.ThirdParty.TauCeti.Cocharacter.limit_apply_eq_coeff_conjugate` and
  `CFSG.ThirdParty.TauCeti.Cocharacter.coeff_coeff_conjugate_conjugate`;
* `TauCeti/Algebra/AlgebraicGroup/Dynamic/Points.lean` and
  `TauCeti/Algebra/AlgebraicGroup/Dynamic/Opposite.lean`:
  `CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter_apply`,
  `CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter_oppositeCocharacter`,
  `CFSG.ThirdParty.TauCeti.Cocharacter.pointsHom_oppositeCocharacter`,
  `CFSG.ThirdParty.TauCeti.Cocharacter.genericPoint_oppositeCocharacter`,
  `CFSG.ThirdParty.TauCeti.Cocharacter.conjugate_oppositeCocharacter`,
  `CFSG.ThirdParty.TauCeti.Cocharacter.levi_oppositeCocharacter` and
  `CFSG.ThirdParty.TauCeti.Cocharacter.parabolic_inf_oppositeCocharacter`.

The natural-isomorphism packagings `parabolicPointsIso`, `unipotentPointsIso` and
`leviPointsIso` are not ported, since the declarations above do not need them.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.

## Adaptations to the pinned API

* Every ported declaration is placed in a namespace rooted at `CFSG.ThirdParty.TauCeti`;
  references to ported declarations are correspondingly qualified.
* The pinned point constructions `TauCeti.Cocharacter.conjugate`,
  `TauCeti.Cocharacter.parabolic`, `TauCeti.Cocharacter.levi`,
  `TauCeti.Cocharacter.unipotent`, `TauCeti.Cocharacter.limit`,
  `TauCeti.Cocharacter.extend`, `TauCeti.Cocharacter.constPoint` and
  `TauCeti.Cocharacter.ofPolyPoint` (file `Dynamic/Parabolic.lean`) are reused rather than
  redefined.
* The opposite cocharacter is the pinned `CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter`
  from `CFSG/ThirdParty/TauCeti/OppositeCocharacter.lean`; that definition is marked
  `@[expose]` so its coordinate formula and the point formulas below are proved from its body.
  Upstream writes `l.oppositeCocharacter`, but dot notation does not resolve to the
  `CFSG.ThirdParty.TauCeti`-namespaced declaration, so the ported statements write the
  application `CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter l` explicitly.
* The pinned lemma `TauCeti.HopfIdeal.ker_tensorProduct_map_eq_leftTensorIdeal_sup_rightTensorIdeal`
  replaces the new `AlgHom.ker_tensorProduct_map_eq_leftTensorIdeal_sup_rightTensorIdeal`.
  The new `Ideal.leftTensorIdeal` and `Ideal.rightTensorIdeal` are written
  `HopfIdeal.leftTensorIdeal` and `HopfIdeal.rightTensorIdeal` at the pin.
* The pinned lemma `TauCeti.AlgHom.convInv_apply` replaces the new
  `WithConv.algHom_inv_apply`.
* The pinned `TauCeti.AlgHom.mapDomain` and `TauCeti.AlgHom.mapDomain_apply` replace the new
  `BialgHom.mapDomain` and `BialgHom.mapDomain_apply`.
* The pinned unit `TauCeti.MultiplicativeGroup.genericUnit` (with `genericUnit_val`,
  `genericUnit_inv` and `genericUnit_zpow_val`) replaces the new
  `LaurentPolynomial.genericUnit` family.
* The pinned `TauCeti.AlgHom.mapValue` replaces the new `AlgHom.mapValue`, and the pinned
  `TauCeti.MultiplicativeGroup.point` is identified with `TauCeti.laurentEval` where the
  statements of the new commit use the latter.
* The new files `Dynamic/Points.lean`, `Dynamic/Opposite.lean` and
  `Algebra/Polynomial/Laurent/Polynomial.lean` are not at the pin. Only the declarations
  needed by the theorems above are ported, in the same file: the negative-coefficient
  criterion for the dynamic parabolic, the coefficient formula for the dynamic limit, the
  cocycle identity for generic conjugation on coefficients, the extension criterion for
  Laurent-valued algebra homomorphisms, and the opposite-cocharacter point formulas.
-/
public section

open CategoryTheory WithConv
open scoped TensorProduct
open _root_.TauCeti
open _root_.TauCeti.HopfIdeal
open _root_.TauCeti.AlgHom
open _root_.TauCeti.CommHopfAlgCat

namespace CFSG.ThirdParty.TauCeti.HopfIdeal

universe u v

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]

/-- An ideal cutting out subgroups over every value algebra is a Hopf ideal. The subgroup
family need not be given separate naturality data: its equations already imply naturality. -/
noncomputable def ofIdealOfPointsSubgroup (I : Ideal H)
    (S : ∀ A : CommAlgCat.{v} R, Subgroup (WithConv (H →ₐ[R] A)))
    (hS : ∀ (A : CommAlgCat.{v} R) (g : WithConv (H →ₐ[R] A)),
      g ∈ S A ↔ I ≤ RingHom.ker g.ofConv) : HopfIdeal R H := by
  let Q := H ⧸ I
  let q : H →ₐ[R] Q := Ideal.Quotient.mkₐ R I
  have hqker : RingHom.ker q = I := by
    rw [← RingHom.ker_coe_toRingHom]
    exact Ideal.Quotient.mkₐ_ker R I
  have hq : I ≤ RingHom.ker q := hqker.symm.le
  have hcomul {x : H} (hx : x ∈ I) :
      Coalgebra.comul (R := R) x ∈ leftTensorIdeal (R := R) (H := H) I ⊔
        rightTensorIdeal (R := R) (H := H) I := by
    let A := CommAlgCat.of R (Q ⊗[R] Q)
    let g : WithConv (H →ₐ[R] A) :=
      toConv ((Algebra.TensorProduct.includeLeft : Q →ₐ[R] Q ⊗[R] Q).comp q)
    let h : WithConv (H →ₐ[R] A) :=
      toConv ((Algebra.TensorProduct.includeRight : Q →ₐ[R] Q ⊗[R] Q).comp q)
    have hg : g ∈ S A := (hS A g).mpr fun y hy ↦ by
      simp only [g, AlgHom.comp_apply, RingHom.mem_ker]
      rw [RingHom.mem_ker.mp (hq hy), map_zero]
    have hh : h ∈ S A := (hS A h).mpr fun y hy ↦ by
      simp only [h, AlgHom.comp_apply, RingHom.mem_ker]
      rw [RingHom.mem_ker.mp (hq hy), map_zero]
    have hzero := RingHom.mem_ker.mp ((hS A (g * h)).mp ((S A).mul_mem hg hh) hx)
    have hmap : Algebra.TensorProduct.lift g.ofConv h.ofConv (fun _ _ ↦ .all ..) =
        Algebra.TensorProduct.map q q := by
      dsimp [g, h, A]
      ext a <;> simp
    rw [AlgHom.convMul_apply, hmap] at hzero
    have hker := ker_tensorProduct_map_eq_leftTensorIdeal_sup_rightTensorIdeal
      q q (Ideal.Quotient.mkₐ_surjective R I) (Ideal.Quotient.mkₐ_surjective R I)
    rw [hqker] at hker
    exact hker ▸ RingHom.mem_ker.mpr hzero
  have hcounit {x : H} (hx : x ∈ I) : Coalgebra.counit (R := R) x = 0 := by
    have hz := RingHom.mem_ker.mp ((hS (CommAlgCat.of R H) 1).mp
      ((S (CommAlgCat.of R H)).one_mem) hx)
    have hc := congrArg (Bialgebra.counitAlgHom R H) hz
    simpa only [AlgHom.convOne_apply, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, map_zero] using hc
  have hantipode {x : H} (hx : x ∈ I) : HopfAlgebra.antipode R x ∈ I := by
    have hg : toConv q ∈ S (CommAlgCat.of R Q) :=
      (hS _ _).mpr hq
    have hz := RingHom.mem_ker.mp ((hS _ _).mp ((S _).inv_mem hg) hx)
    rw [_root_.TauCeti.AlgHom.convInv_apply] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  exact ofIdeal I (fun _ hx ↦ hcomul hx) (fun _ hx ↦ hcounit hx)
    (fun _ hx ↦ hantipode hx)

/-- The pointwise construction leaves the defining ideal unchanged. -/
@[simp]
theorem ofIdealOfPointsSubgroup_toIdeal (I : Ideal H) (S hS) :
    (ofIdealOfPointsSubgroup (R := R) I S hS).toIdeal = I := (rfl)

end CFSG.ThirdParty.TauCeti.HopfIdeal

namespace CFSG.ThirdParty.TauCeti

universe u v w

variable {R : Type u} {A : Type v} {H : Type w}

/-- A Laurent polynomial comes from a polynomial exactly when its negative coefficients
vanish. -/
@[simp]
theorem exists_toLaurent_eq_iff [Semiring A] {p : LaurentPolynomial A} :
    (∃ q : Polynomial A, q.toLaurent = p) ↔ ∀ n : ℤ, n < 0 → p.coeff n = 0 := by
  rw [← Set.mem_range]
  have hcast (n : ℤ) : n ∉ Set.range (Nat.cast : ℕ → ℤ) ↔ n < 0 := by
    constructor
    · intro hn
      by_contra h
      exact hn ⟨n.toNat, Int.toNat_of_nonneg (by omega)⟩
    · rintro hn ⟨m, hm⟩
      omega
  have hrange : p ∈ Set.range Polynomial.toLaurent ↔
      p.coeff ∈ Set.range (Finsupp.mapDomain (Nat.cast : ℕ → ℤ)) := by
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.toFinsupp.coeff, rfl⟩
    · rintro ⟨q, hq⟩
      refine ⟨Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff q), ?_⟩
      exact AddMonoidAlgebra.coeff_injective hq
  rw [hrange, Finsupp.mem_range_mapDomain_iff (Nat.cast : ℕ → ℤ) Nat.cast_injective]
  exact forall_congr' fun n ↦ imp_congr_left (hcast n)

variable [CommSemiring R]

/-- A Laurent-valued algebra homomorphism extends to polynomial values exactly when all its
negative coefficients vanish. -/
theorem exists_algHom_toLaurent_comp_eq_iff [CommSemiring A] [Semiring H]
    [Algebra R A] [Algebra R H] {f : H →ₐ[R] LaurentPolynomial A} :
    (∃ F : H →ₐ[R] Polynomial A,
      (Polynomial.toLaurentAlg.restrictScalars R).comp F = f) ↔
      ∀ h : H, ∀ n : ℤ, n < 0 → (f h).coeff n = 0 := by
  constructor
  · rintro ⟨F, rfl⟩ h
    exact exists_toLaurent_eq_iff.mp ⟨F h, rfl⟩
  · intro hf
    let i : Polynomial A →ₐ[R] LaurentPolynomial A :=
      Polynomial.toLaurentAlg.restrictScalars R
    let e := AlgEquiv.ofInjective i Polynomial.toLaurent_injective
    let F := e.symm.toAlgHom.comp (f.codRestrict i.range fun h ↦
      exists_toLaurent_eq_iff.mpr (hf h))
    refine ⟨F, AlgHom.ext fun h ↦ ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply (f.codRestrict i.range _ h))

end CFSG.ThirdParty.TauCeti



namespace CFSG.ThirdParty.TauCeti.Cocharacter

open WithConv
open _root_.TauCeti.Cocharacter

universe u v w

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable {A : Type w} [CommRing A] [Algebra R A]

/-- Universal conjugation by a cocharacter, evaluated at the identity algebra homomorphism
(the universal point of the ambient group, not its identity element). -/
noncomputable def conjugationAlgHom (l : H →ₐc[R] LaurentPolynomial R) :
    H →ₐ[R] LaurentPolynomial H :=
  (conjugate H l (toConv (AlgHom.id R H))).ofConv

/-- The coefficients of conjugation at any point are evaluations of the universal coefficients. -/
theorem coeff_conjugate (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] A)) (h : H) (n : ℤ) :
    ((conjugate A l g).ofConv h).coeff n = g.ofConv ((conjugationAlgHom l h).coeff n) := by
  have heq := mapValue_conjugate_mapAlgHom (A := H) (B := A) (φ := g.ofConv) (l := l)
    (g := toConv (AlgHom.id R H))
  simp only [AlgHom.mapValue_apply, AlgHom.comp_id, toConv_ofConv] at heq
  have hc := congrArg (fun p : WithConv (H →ₐ[R] LaurentPolynomial A) ↦
    (p.ofConv h).coeff n) heq
  simpa only [AddMonoidAlgebra.coeff_mapAlgHom, AlgHom.comp_apply, conjugationAlgHom] using hc.symm

/-- Evaluating generic conjugation at the Laurent parameter one recovers the original point. -/
theorem mapValue_laurentEval_one_conjugate (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] A)) :
    AlgHom.mapValue ((laurentEval (R := A) (1 : Aˣ)).restrictScalars R)
      (conjugate A l g) = g := by
  set e : LaurentPolynomial A →ₐ[R] A := (laurentEval (R := A) (1 : Aˣ)).restrictScalars R
  rw [mapValue_conjugate]
  have hu : Units.map e.toMonoidHom (MultiplicativeGroup.genericUnit A) = 1 := by
    ext
    simp [e]
  have hc : e.comp (IsScalarTower.toAlgHom R A (LaurentPolynomial A)) = AlgHom.id R A := by
    ext a
    simp [e]
  rw [hu, hc]
  simp

/-- Membership in the dynamic parabolic is the vanishing of every negative coefficient of the
conjugation family. -/
theorem mem_parabolic_iff_forall_coeff_conjugate_eq_zero (l : H →ₐc[R] LaurentPolynomial R)
    {g : WithConv (H →ₐ[R] A)} :
    g ∈ parabolic A l ↔
      ∀ h : H, ∀ n : ℤ, n < 0 → ((conjugate A l g).ofConv h).coeff n = 0 := by
  rw [mem_parabolic_iff, ← exists_algHom_toLaurent_comp_eq_iff]
  constructor
  · rintro ⟨F, hF⟩
    rw [ofPolyPoint_apply] at hF
    exact ⟨F.ofConv, congrArg ofConv hF⟩
  · rintro ⟨F, hF⟩
    refine ⟨toConv F, ?_⟩
    rw [ofPolyPoint_apply]
    exact congrArg toConv hF

/-- The dynamic limit evaluates the constant coefficient of the conjugation family. -/
theorem limit_apply_eq_coeff_conjugate (l : H →ₐc[R] LaurentPolynomial R)
    (g : parabolic A l) (h : H) :
    (limit A l g).ofConv h = ((conjugate A l g.1).ofConv h).coeff 0 := by
  rw [← ofPolyPoint_extend g, ofPolyPoint_apply, limit_apply, evalZeroPoint_apply]
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Polynomial.coe_toLaurentAlg, Polynomial.coe_aeval_eq_eval,
    ← Polynomial.coeff_zero_eq_eval_zero, LaurentPolynomial.coeff_toLaurent]
  exact (Finsupp.mapDomain_apply_of_injective
    (Nat.castEmbedding (R := ℤ)).injective _ 0).symm

section LeviRetraction

variable (R A) in
/-- The unit `T · T'` of `A[T;T⁻¹][T';T'⁻¹]`, the product of the two Laurent variables. -/
private noncomputable def prodUnit : (LaurentPolynomial (LaurentPolynomial A))ˣ :=
  Units.map (IsScalarTower.toAlgHom R (LaurentPolynomial A)
      (LaurentPolynomial (LaurentPolynomial A))).toMonoidHom
        (MultiplicativeGroup.genericUnit A) *
    MultiplicativeGroup.genericUnit (LaurentPolynomial A)

variable (R A) in
/-- The substitution `T ↦ T · T'`, as an `R`-algebra homomorphism
`A[T;T⁻¹] → A[T;T⁻¹][T';T'⁻¹]`. -/
private noncomputable def prodSubst :
    LaurentPolynomial A →ₐ[R] LaurentPolynomial (LaurentPolynomial A) :=
  (laurentEval (R := A) (prodUnit R A)).restrictScalars R

variable (R A) in
private theorem prodSubst_C (a : A) :
    prodSubst R A (LaurentPolynomial.C a) =
      LaurentPolynomial.C (LaurentPolynomial.C a) :=
  laurentEval_C (R := A) _ a

variable (R A) in
private theorem prodSubst_T :
    prodSubst R A (LaurentPolynomial.T 1) =
      (prodUnit R A : LaurentPolynomial (LaurentPolynomial A)) :=
  (laurentEval_T (R := A) (prodUnit R A) 1).trans (by rw [zpow_one])

variable (R A) in
private theorem map_prodSubst_genericUnit :
    Units.map (prodSubst R A).toMonoidHom
        (MultiplicativeGroup.genericUnit A) = prodUnit R A :=
  Units.ext (by
    rw [Units.coe_map, MultiplicativeGroup.genericUnit_val]
    exact prodSubst_T (R := R) A)

variable (R A) in
private theorem prodSubst_comp_const :
    (prodSubst R A).comp (IsScalarTower.toAlgHom R A (LaurentPolynomial A)) =
      (IsScalarTower.toAlgHom R (LaurentPolynomial A)
        (LaurentPolynomial (LaurentPolynomial A))).comp
          (IsScalarTower.toAlgHom R A (LaurentPolynomial A)) :=
  AlgHom.ext fun a ↦ prodSubst_C R A a

variable (R A) in
private theorem prodUnit_val :
    (prodUnit R A : LaurentPolynomial (LaurentPolynomial A)) =
      LaurentPolynomial.C (LaurentPolynomial.T 1) * LaurentPolynomial.T 1 := by
  rw [prodUnit, Units.val_mul, Units.coe_map]
  simp

variable (R A) in
/-- The substitution `T ↦ T · T'` sends the monomial `a Tⁿ` to `(a Tⁿ) T'ⁿ`. -/
private theorem prodSubst_C_mul_T (a : A) (n : ℤ) :
    prodSubst R A (LaurentPolynomial.C a * LaurentPolynomial.T n) =
      LaurentPolynomial.C (LaurentPolynomial.C a * LaurentPolynomial.T n) *
        LaurentPolynomial.T n := by
  have hT : prodSubst R A (LaurentPolynomial.T n) =
      LaurentPolynomial.C (LaurentPolynomial.T n) * LaurentPolynomial.T n := by
    have hc : Commute
        (Units.map (IsScalarTower.toAlgHom R (LaurentPolynomial A)
          (LaurentPolynomial (LaurentPolynomial A))).toMonoidHom
            (MultiplicativeGroup.genericUnit A))
        (MultiplicativeGroup.genericUnit (LaurentPolynomial A)) :=
      Units.ext (mul_comm _ _)
    rw [prodSubst, AlgHom.restrictScalars_apply, laurentEval_T, prodUnit, hc.mul_zpow,
      Units.val_mul, ← map_zpow, Units.coe_map, MultiplicativeGroup.genericUnit_zpow_val,
      MultiplicativeGroup.genericUnit_zpow_val]
    simp
  rw [map_mul, prodSubst_C R A, hT, map_mul, mul_assoc]

variable (R A) in
/-- The coefficients of the substitution `T ↦ T · T'` are concentrated on the diagonal. -/
private theorem coeff_coeff_prodSubst (p : LaurentPolynomial A) (m n : ℤ) :
    ((prodSubst R A p).coeff n).coeff m = if m = n then p.coeff n else 0 := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
      split_ifs <;> simp
  | C_mul_T k a =>
      rw [prodSubst_C_mul_T R A, ← LaurentPolynomial.single_eq_C_mul_T,
        ← LaurentPolynomial.single_eq_C_mul_T]
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      split_ifs <;> simp_all [-LaurentPolynomial.single_eq_C_mul_T]

/-- **The cocycle identity for generic conjugation**: conjugating by `l(T)` and then by `l(T')`
is conjugating by `l(T · T')`. -/
private theorem conjugate_conjugate (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] A)) :
    conjugate (LaurentPolynomial A) l (conjugate A l g) =
      AlgHom.mapValue (prodSubst R A) (conjugate A l g) := by
  rw [conjugate_apply, constPoint_apply, ← AlgHom.mapValue_apply,
    mapValue_conjugate, genericPoint_eq_pointsHom]
  have hconj (a b x : WithConv (H →ₐ[R]
      LaurentPolynomial (LaurentPolynomial A))) :
      a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by
    simpa only [MulAut.conj_apply, MulAut.mul_apply] using
      congrArg (fun f : MulAut _ ↦ f x)
        ((MulAut.conj : _ →* MulAut _).map_mul a b)
  rw [← hconj, ← map_mul, mapValue_conjugate, map_prodSubst_genericUnit R A,
    prodSubst_comp_const, prodUnit, mul_comm
      (Units.map (IsScalarTower.toAlgHom R (LaurentPolynomial A)
        (LaurentPolynomial (LaurentPolynomial A))).toMonoidHom
          (MultiplicativeGroup.genericUnit A))
      (MultiplicativeGroup.genericUnit (LaurentPolynomial A))]

/-- **The cocycle identity for generic conjugation, on coefficients.** Conjugating
`l(T) · g · l(T)⁻¹` once more by `l(T')` only produces monomials in `T · T'`: the coefficient of
`T'ⁿ Tᵐ` is the coefficient of `Tⁿ` in `l(T) · g · l(T)⁻¹` when `m = n`, and zero otherwise. -/
theorem coeff_coeff_conjugate_conjugate (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] A)) (h : H) (m n : ℤ) :
    (((conjugate (LaurentPolynomial A) l (conjugate A l g)).ofConv h).coeff n).coeff m =
      if m = n then ((conjugate A l g).ofConv h).coeff n else 0 := by
  rw [conjugate_conjugate, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
    coeff_coeff_prodSubst]

end LeviRetraction

/-- **The coefficients of universal conjugation are weight vectors.** Conjugating the `n`-th
coefficient of `h` produces only the monomial of degree `n`, whose coefficient is that same
coefficient. -/
@[simp]
theorem coeff_conjugationAlgHom_coeff (l : H →ₐc[R] LaurentPolynomial R) (h : H) (m n : ℤ) :
    (conjugationAlgHom l ((conjugationAlgHom l h).coeff n)).coeff m =
      if m = n then (conjugationAlgHom l h).coeff n else 0 := by
  have h' := coeff_coeff_conjugate_conjugate (A := H) (l := l) (toConv (AlgHom.id R H)) h m n
  rwa [coeff_conjugate] at h'

/-- Conjugation by the generic point sends the `n`-th coefficient of universal conjugation to a
monomial of degree `n`. -/
theorem conjugate_ofConv_coeff_conjugationAlgHom (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] A)) (h : H) (n : ℤ) :
    (conjugate A l g).ofConv ((conjugationAlgHom l h).coeff n) =
      LaurentPolynomial.C (g.ofConv ((conjugationAlgHom l h).coeff n)) *
        LaurentPolynomial.T n := by
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun m ↦ ?_)
  rw [coeff_conjugate, coeff_conjugationAlgHom_coeff, ← LaurentPolynomial.single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs <;> simp_all [eq_comm]

end CFSG.ThirdParty.TauCeti.Cocharacter

namespace CFSG.ThirdParty.TauCeti.Cocharacter

open WithConv
open _root_.TauCeti.Cocharacter

universe u v w

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable {A : Type w} [CommRing A] [Algebra R A]

private noncomputable def negativeCoefficientIdeal (l : H →ₐc[R] LaurentPolynomial R) : Ideal H :=
  Ideal.span {x | ∃ h : H, ∃ n : ℤ, n < 0 ∧ (conjugationAlgHom l h).coeff n = x}

private theorem negativeCoefficientIdeal_le_ker_iff
    (l : H →ₐc[R] LaurentPolynomial R) (g : WithConv (H →ₐ[R] A)) :
    negativeCoefficientIdeal l ≤ RingHom.ker g.ofConv ↔ g ∈ parabolic A l := by
  rw [negativeCoefficientIdeal, Ideal.span_le, mem_parabolic_iff_forall_coeff_conjugate_eq_zero]
  constructor
  · intro hg h n hn
    rw [coeff_conjugate]
    exact RingHom.mem_ker.mp (hg ⟨h, n, hn, rfl⟩)
  · rintro hg x ⟨h, n, hn, rfl⟩
    exact RingHom.mem_ker.mpr ((coeff_conjugate (g := g) l h n).symm.trans (hg h n hn))

/-- The defining Hopf ideal of the dynamic parabolic, generated by the negative coefficients
of universal conjugation. -/
noncomputable def parabolicDefiningHopfIdeal (l : H →ₐc[R] LaurentPolynomial R) :
    HopfIdeal R H :=
  CFSG.ThirdParty.TauCeti.HopfIdeal.ofIdealOfPointsSubgroup (negativeCoefficientIdeal l)
    (fun A ↦ parabolic A l) (fun _ g ↦ (negativeCoefficientIdeal_le_ker_iff l g).symm)

/-- The ideal defining the dynamic parabolic is generated by the negative Laurent coefficients. -/
@[simp]
theorem parabolicDefiningHopfIdeal_toIdeal (l : H →ₐc[R] LaurentPolynomial R) :
    (parabolicDefiningHopfIdeal l).toIdeal =
      Ideal.span {x | ∃ h : H, ∃ n : ℤ, n < 0 ∧ (conjugationAlgHom l h).coeff n = x} := by
  rw [parabolicDefiningHopfIdeal,
    CFSG.ThirdParty.TauCeti.HopfIdeal.ofIdealOfPointsSubgroup_toIdeal]
  rfl

/-- Membership in the defining Hopf ideal is membership in the span of the negative coefficients. -/
@[simp]
theorem mem_parabolicDefiningHopfIdeal (l : H →ₐc[R] LaurentPolynomial R) (x : H) :
    x ∈ parabolicDefiningHopfIdeal l ↔
      x ∈ Ideal.span {x | ∃ h : H, ∃ n : ℤ, n < 0 ∧ (conjugationAlgHom l h).coeff n = x} := by
  rw [← mem_toIdeal, parabolicDefiningHopfIdeal_toIdeal]

/-- All negative coefficients of universal conjugation vanish on the dynamic parabolic. -/
theorem coeff_conjugationAlgHom_mem_parabolicDefiningHopfIdeal
    (l : H →ₐc[R] LaurentPolynomial R) (h : H) {n : ℤ} (hn : n < 0) :
    (conjugationAlgHom l h).coeff n ∈ parabolicDefiningHopfIdeal l := by
  rw [← mem_toIdeal, parabolicDefiningHopfIdeal_toIdeal]
  exact Ideal.subset_span ⟨h, n, hn, rfl⟩

/-- The dynamic parabolic is represented by the closed subgroup defined by its coefficient ideal. -/
@[simp]
theorem quotientPointsSubgroup_parabolicDefiningHopfIdeal
    (l : H →ₐc[R] LaurentPolynomial R) :
    quotientPointsSubgroup (CommHopfAlgCat.of R H)
      (parabolicDefiningHopfIdeal l) (CommAlgCat.of R A) = parabolic A l := by
  ext g
  rw [mem_quotientPointsSubgroup_iff]
  have hker : (∀ x ∈ parabolicDefiningHopfIdeal l, g.ofConv x = 0) ↔
      (parabolicDefiningHopfIdeal l).toIdeal ≤ RingHom.ker g.ofConv := by
    simp only [IsConcreteLE.le_iff, mem_toIdeal, RingHom.mem_ker]
  rw [hker, parabolicDefiningHopfIdeal_toIdeal]
  exact negativeCoefficientIdeal_le_ker_iff l g

/-- The coefficient ideal is the smallest Hopf ideal containing all the negative coefficients. -/
theorem parabolicDefiningHopfIdeal_le_iff (l : H →ₐc[R] LaurentPolynomial R)
    (I : HopfIdeal R H) :
    parabolicDefiningHopfIdeal l ≤ I ↔
      ∀ h : H, ∀ n : ℤ, n < 0 → (conjugationAlgHom l h).coeff n ∈ I := by
  rw [← toIdeal_le_toIdeal, parabolicDefiningHopfIdeal_toIdeal, Ideal.span_le]
  constructor
  · intro hi h n hn
    exact hi ⟨h, n, hn, rfl⟩
  · rintro hi x ⟨h, n, hn, rfl⟩
    exact hi h n hn

end CFSG.ThirdParty.TauCeti.Cocharacter

namespace CFSG.ThirdParty.TauCeti.BialgHom

open WithConv
open _root_.TauCeti.Cocharacter
open CFSG.ThirdParty.TauCeti.Cocharacter

universe u v w

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable {A : Type w} [CommRing A] [Algebra R A]

/-- If the dynamic parabolic of a cocharacter is the whole group, then its points over every
value algebra are all the points. -/
theorem parabolic_eq_top_of_parabolicDefiningHopfIdeal_eq_bot
    (l : H →ₐc[R] LaurentPolynomial R) (hl : parabolicDefiningHopfIdeal l = ⊥)
    (A : Type*) [CommRing A] [Algebra R A] :
    parabolic A l = ⊤ := by
  rw [← quotientPointsSubgroup_parabolicDefiningHopfIdeal, hl, quotientPointsSubgroup_bot]

/-- A parabolic point has trivial dynamic limit exactly when it annihilates the differences
between the universal constant coefficients and the counit. -/
theorem limit_eq_one_iff_coeff_conjugationAlgHom
    (l : H →ₐc[R] LaurentPolynomial R) (g : parabolic A l) :
    limit A l g = 1 ↔ ∀ h : H,
      g.1.ofConv ((conjugationAlgHom l h).coeff 0 -
        algebraMap R H (Coalgebra.counit h)) = 0 := by
  have hvalue (h : H) :
      g.1.ofConv ((conjugationAlgHom l h).coeff 0 -
          algebraMap R H (Coalgebra.counit h)) =
        (limit A l g).ofConv h - (1 : WithConv (H →ₐ[R] A)).ofConv h := by
    rw [map_sub, AlgHom.commutes, limit_apply_eq_coeff_conjugate, coeff_conjugate,
      AlgHom.convOne_apply]
  simp only [hvalue, sub_eq_zero]
  constructor
  · intro hg h
    rw [hg]
  · intro hg
    exact congrArg toConv (AlgHom.ext hg)

/-- The parabolic equations and the constant-coefficient equations for trivial limit. -/
private noncomputable def unipotentCoefficientIdeal
    (l : H →ₐc[R] LaurentPolynomial R) : Ideal H :=
  (parabolicDefiningHopfIdeal l).toIdeal ⊔
    Ideal.span {x | ∃ h : H, (conjugationAlgHom l h).coeff 0 -
      algebraMap R H (Coalgebra.counit h) = x}

private theorem unipotentCoefficientIdeal_le_ker_iff
    (l : H →ₐc[R] LaurentPolynomial R) (g : WithConv (H →ₐ[R] A)) :
    unipotentCoefficientIdeal l ≤ RingHom.ker g.ofConv ↔ g ∈ unipotent A l := by
  have hP : (parabolicDefiningHopfIdeal l).toIdeal ≤ RingHom.ker g.ofConv ↔
      g ∈ parabolic A l := by
    rw [← quotientPointsSubgroup_parabolicDefiningHopfIdeal,
      mem_quotientPointsSubgroup_iff]
    simp only [IsConcreteLE.le_iff, mem_toIdeal, RingHom.mem_ker]
  rw [unipotentCoefficientIdeal, sup_le_iff, hP, Ideal.span_le, mem_unipotent_iff]
  constructor
  · rintro ⟨hg, hcoeff⟩
    refine ⟨hg, (limit_eq_one_iff_coeff_conjugationAlgHom l ⟨g, hg⟩).mpr ?_⟩
    intro h
    exact RingHom.mem_ker.mp (hcoeff ⟨h, rfl⟩)
  · rintro ⟨hg, hlimit⟩
    refine ⟨hg, ?_⟩
    rintro x ⟨h, rfl⟩
    exact RingHom.mem_ker.mpr
      ((limit_eq_one_iff_coeff_conjugationAlgHom l ⟨g, hg⟩).mp hlimit h)

/-- The defining Hopf ideal of the dynamic unipotent subgroup: the parabolic equations,
together with the equations setting the dynamic limit equal to the identity. -/
noncomputable def unipotentDefiningHopfIdeal (l : H →ₐc[R] LaurentPolynomial R) :
    HopfIdeal R H :=
  CFSG.ThirdParty.TauCeti.HopfIdeal.ofIdealOfPointsSubgroup (unipotentCoefficientIdeal l)
    (fun A ↦ unipotent A l) (fun _ g ↦ (unipotentCoefficientIdeal_le_ker_iff l g).symm)

/-- The underlying ideal is generated by the parabolic ideal and the constant-coefficient
differences from the counit. -/
@[simp]
theorem unipotentDefiningHopfIdeal_toIdeal (l : H →ₐc[R] LaurentPolynomial R) :
    (unipotentDefiningHopfIdeal l).toIdeal =
      (parabolicDefiningHopfIdeal l).toIdeal ⊔
        Ideal.span {x | ∃ h : H, (conjugationAlgHom l h).coeff 0 -
          algebraMap R H (Coalgebra.counit h) = x} := by
  rw [unipotentDefiningHopfIdeal,
    CFSG.ThirdParty.TauCeti.HopfIdeal.ofIdealOfPointsSubgroup_toIdeal]
  rfl

/-- Membership in the unipotent defining ideal is membership in its coefficient ideal. -/
@[simp]
theorem mem_unipotentDefiningHopfIdeal (l : H →ₐc[R] LaurentPolynomial R) (x : H) :
    x ∈ unipotentDefiningHopfIdeal l ↔
      x ∈ (parabolicDefiningHopfIdeal l).toIdeal ⊔
        Ideal.span {x | ∃ h : H, (conjugationAlgHom l h).coeff 0 -
          algebraMap R H (Coalgebra.counit h) = x} := by
  rw [← mem_toIdeal, unipotentDefiningHopfIdeal_toIdeal]

/-- The dynamic unipotent defining ideal contains the parabolic defining ideal. -/
theorem parabolicDefiningHopfIdeal_le_unipotentDefiningHopfIdeal
    (l : H →ₐc[R] LaurentPolynomial R) :
    parabolicDefiningHopfIdeal l ≤ unipotentDefiningHopfIdeal l := by
  rw [← toIdeal_le_toIdeal, unipotentDefiningHopfIdeal_toIdeal]
  exact le_sup_left

/-- The constant coefficient of universal conjugation equals the counit on the dynamic
unipotent subgroup. -/
theorem coeff_conjugationAlgHom_sub_counit_mem_unipotentDefiningHopfIdeal
    (l : H →ₐc[R] LaurentPolynomial R) (h : H) :
    (conjugationAlgHom l h).coeff 0 - algebraMap R H (Coalgebra.counit h) ∈
      unipotentDefiningHopfIdeal l := by
  rw [← mem_toIdeal, unipotentDefiningHopfIdeal_toIdeal]
  exact Ideal.mem_sup_right (Ideal.subset_span ⟨h, rfl⟩)

/-- The unipotent ideal is the smallest Hopf ideal containing the parabolic ideal and
all constant-coefficient differences from the counit. -/
theorem unipotentDefiningHopfIdeal_le_iff (l : H →ₐc[R] LaurentPolynomial R)
    (I : HopfIdeal R H) :
    unipotentDefiningHopfIdeal l ≤ I ↔
      parabolicDefiningHopfIdeal l ≤ I ∧ ∀ h : H,
        (conjugationAlgHom l h).coeff 0 - algebraMap R H (Coalgebra.counit h) ∈ I := by
  rw [← toIdeal_le_toIdeal, unipotentDefiningHopfIdeal_toIdeal,
    sup_le_iff, toIdeal_le_toIdeal, Ideal.span_le]
  exact and_congr_right fun _ ↦ ⟨fun hi h ↦ hi ⟨h, rfl⟩, by
    rintro hi x ⟨h, rfl⟩
    exact hi h⟩

/-- The points cut out by the coefficient ideal are exactly the dynamic unipotent subgroup. -/
@[simp]
theorem quotientPointsSubgroup_unipotentDefiningHopfIdeal
    (l : H →ₐc[R] LaurentPolynomial R) :
    quotientPointsSubgroup (CommHopfAlgCat.of R H)
      (unipotentDefiningHopfIdeal l) (CommAlgCat.of R A) = unipotent A l := by
  ext g
  rw [mem_quotientPointsSubgroup_iff]
  have hker : (∀ x ∈ unipotentDefiningHopfIdeal l, g.ofConv x = 0) ↔
      (unipotentDefiningHopfIdeal l).toIdeal ≤ RingHom.ker g.ofConv := by
    simp only [IsConcreteLE.le_iff, mem_toIdeal, RingHom.mem_ker]
  rw [hker, unipotentDefiningHopfIdeal_toIdeal]
  exact unipotentCoefficientIdeal_le_ker_iff l g

/-- If the dynamic parabolic of a cocharacter is the whole group, then the dynamic unipotent
subgroup is a normal closed subgroup of the whole group. -/
theorem isNormal_unipotentDefiningHopfIdeal_of_parabolicDefiningHopfIdeal_eq_bot
    (l : H →ₐc[R] LaurentPolynomial R) (hl : parabolicDefiningHopfIdeal l = ⊥) :
    (unipotentDefiningHopfIdeal l).IsNormal := by
  rw [isNormal_iff_quotientPointsSubgroup_normal (CommHopfAlgCat.of R H)]
  rintro ⟨A⟩
  rw [quotientPointsSubgroup_unipotentDefiningHopfIdeal]
  refine ⟨fun u hu g ↦ conj_mem_unipotent ?_ hu⟩
  rw [parabolic_eq_top_of_parabolicDefiningHopfIdeal_eq_bot l hl]
  exact Subgroup.mem_top g

end CFSG.ThirdParty.TauCeti.BialgHom


namespace CFSG.ThirdParty.TauCeti.Cocharacter

open WithConv
open _root_.TauCeti.Cocharacter
open _root_.TauCeti.CommHopfAlgCat

universe u v w

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]

/-- The Hopf ideal cutting out the dynamic Levi, the scheme-theoretic intersection of the
parabolics of a cocharacter and its opposite. -/
noncomputable def leviDefiningHopfIdeal (l : H →ₐc[R] LaurentPolynomial R) :
    HopfIdeal R H :=
  parabolicDefiningHopfIdeal l ⊔
    parabolicDefiningHopfIdeal (CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter l)

/-- The Levi defining ideal is the sum of the two opposite parabolic defining ideals. -/
theorem leviDefiningHopfIdeal_def (l : H →ₐc[R] LaurentPolynomial R) :
    leviDefiningHopfIdeal l =
      parabolicDefiningHopfIdeal l ⊔
        parabolicDefiningHopfIdeal (CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter l) :=
  (rfl)

end CFSG.ThirdParty.TauCeti.Cocharacter

namespace CFSG.ThirdParty.TauCeti.BialgHom

open WithConv
open _root_.TauCeti.Cocharacter

variable {R : Type*} {H : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]

/-- On coordinates the opposite cocharacter inverts the Laurent variable. -/
@[simp]
theorem oppositeCocharacter_apply (l : H →ₐc[R] LaurentPolynomial R) (h : H) :
    oppositeCocharacter l h = LaurentPolynomial.invert (l h) := (rfl)

/-- Taking the opposite cocharacter twice recovers the original one. -/
@[simp]
theorem oppositeCocharacter_oppositeCocharacter (l : H →ₐc[R] LaurentPolynomial R) :
    oppositeCocharacter (oppositeCocharacter l) = l := by
  ext h : 1
  simpa only [oppositeCocharacter_apply] using LaurentPolynomial.involutive_invert (l h)

end CFSG.ThirdParty.TauCeti.BialgHom

namespace CFSG.ThirdParty.TauCeti.Cocharacter

open WithConv
open _root_.TauCeti.Cocharacter

universe u v w

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable {A : Type w} [CommRing A] [Algebra R A]

private theorem point_invert (R : Type*) [CommSemiring R]
    (A : Type*) [CommSemiring A] [Algebra R A] (u : Aˣ) (p : LaurentPolynomial R) :
    MultiplicativeGroup.point (R := R) (A := A) u (LaurentPolynomial.invert p) =
      MultiplicativeGroup.point (R := R) (A := A) u⁻¹ p := by
  change LaurentPolynomial.eval₂ (algebraMap R A) u (LaurentPolynomial.invert p) =
    LaurentPolynomial.eval₂ (algebraMap R A) u⁻¹ p
  rw [← laurentEval_eq_eval₂, ← laurentEval_eq_eval₂]
  exact laurentEval_invert u p

/-- The opposite cocharacter evaluates at the inverse unit. -/
theorem pointsHom_oppositeCocharacter (l : H →ₐc[R] LaurentPolynomial R) (u : Aˣ) :
    pointsHom A (CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter l) u =
      pointsHom A l u⁻¹ := by
  ext h
  simp only [pointsHom_apply, AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply]
  exact point_invert R A u (l h)

/-- The generic value of the opposite cocharacter is the inverse generic value. -/
@[simp]
theorem genericPoint_oppositeCocharacter (l : H →ₐc[R] LaurentPolynomial R) :
    genericPoint A (CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter l) =
      (genericPoint A l)⁻¹ := by
  simp only [genericPoint_eq_pointsHom, pointsHom_oppositeCocharacter, map_inv]

/-- Reversing the cocharacter inverts the variable of the conjugation family. -/
theorem conjugate_oppositeCocharacter (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] A)) :
    conjugate A (CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter l) g =
      AlgHom.mapValue (LaurentPolynomial.invert.toAlgHom.restrictScalars R)
        (conjugate A l g) := by
  rw [mapValue_conjugate]
  have hu : Units.map (LaurentPolynomial.invert.toAlgHom.restrictScalars R).toMonoidHom
      (MultiplicativeGroup.genericUnit A) = (MultiplicativeGroup.genericUnit A)⁻¹ := by
    ext
    simp [MultiplicativeGroup.genericUnit_val, MultiplicativeGroup.genericUnit_inv]
  have hc : (LaurentPolynomial.invert.toAlgHom.restrictScalars R).comp
      (IsScalarTower.toAlgHom R A (LaurentPolynomial A)) =
      IsScalarTower.toAlgHom R A (LaurentPolynomial A) := by
    ext a : 1
    exact LaurentPolynomial.invert_C a
  rw [hu, hc, map_inv, conjugate_apply, genericPoint_oppositeCocharacter, inv_inv]
  rw [constPoint_apply, AlgHom.mapValue_apply]
  simp only [genericPoint_eq_pointsHom, inv_inv]

/-- Opposite cocharacters have the same Levi subgroup. -/
@[simp]
theorem levi_oppositeCocharacter (l : H →ₐc[R] LaurentPolynomial R) :
    levi A (CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter l) = levi A l := by
  ext g
  simp only [mem_levi_iff, conjugate_apply, genericPoint_oppositeCocharacter,
    mul_inv_eq_iff_eq_mul]
  exact Commute.inv_left_iff

/-- The two opposite dynamic parabolics meet exactly in their common Levi subgroup. -/
@[simp]
theorem parabolic_inf_oppositeCocharacter (l : H →ₐc[R] LaurentPolynomial R) :
    parabolic A l ⊓ parabolic A (CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter l) =
      levi A l := by
  apply le_antisymm
  · intro g hg
    have hc (h : H) : (conjugate A l g).ofConv h =
        LaurentPolynomial.C (((conjugate A l g).ofConv h).coeff 0) := by
      ext n
      rcases lt_trichotomy n 0 with hn | rfl | hn
      · rw [(mem_parabolic_iff_forall_coeff_conjugate_eq_zero l).mp hg.1 h n hn]
        simp only [LaurentPolynomial.C_apply, ne_of_lt hn, ite_false]
      · simp
      · have hz := (mem_parabolic_iff_forall_coeff_conjugate_eq_zero
          (CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter l)).mp hg.2 h (-n)
          (neg_neg_of_pos hn)
        rw [conjugate_oppositeCocharacter] at hz
        simpa [AlgHom.mapValue_apply, ne_of_gt hn] using hz
    let e : LaurentPolynomial A →ₐ[R] A := (laurentEval (R := A) (1 : Aˣ)).restrictScalars R
    have heval : AlgHom.mapValue e (conjugate A l g) = g :=
      mapValue_laurentEval_one_conjugate l g
    rw [mem_levi_iff]
    apply WithConv.ext
    apply AlgHom.ext
    intro h
    have hevalh := congrArg (fun x : WithConv (H →ₐ[R] A) ↦ x.ofConv h) heval
    simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply] at hevalh
    rw [hc] at hevalh
    have hzero : ((conjugate A l g).ofConv h).coeff 0 = g.ofConv h := by
      simpa only [e, AlgHom.restrictScalars_apply, laurentEval_C,
        Algebra.algebraMap_self, RingHom.id_apply] using hevalh
    rw [constPoint_apply]
    exact (hc h).trans (congrArg LaurentPolynomial.C hzero)
  · exact le_inf levi_le_parabolic
      (by rw [← levi_oppositeCocharacter l]; exact levi_le_parabolic)

end CFSG.ThirdParty.TauCeti.Cocharacter

namespace CFSG.ThirdParty.TauCeti.Cocharacter

open WithConv
open _root_.TauCeti.Cocharacter
open _root_.TauCeti.CommHopfAlgCat

universe u v w

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable {A : Type w} [CommRing A] [Algebra R A]

/-- Opposite cocharacters define the same closed Levi subgroup scheme. -/
@[simp]
theorem leviDefiningHopfIdeal_oppositeCocharacter (l : H →ₐc[R] LaurentPolynomial R) :
    leviDefiningHopfIdeal (CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter l) =
      leviDefiningHopfIdeal l := by
  simp only [leviDefiningHopfIdeal_def,
    CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter_oppositeCocharacter, sup_comm]

/-- The subgroup cut out by the Levi ideal is exactly the dynamic Levi, over every value
algebra. -/
@[simp]
theorem quotientPointsSubgroup_leviDefiningHopfIdeal (l : H →ₐc[R] LaurentPolynomial R)
    (A : CommAlgCat.{w} R) :
    quotientPointsSubgroup (CommHopfAlgCat.of R H) (leviDefiningHopfIdeal l) A = levi A l := by
  rw [leviDefiningHopfIdeal_def, quotientPointsSubgroup_sup,
    quotientPointsSubgroup_parabolicDefiningHopfIdeal,
    quotientPointsSubgroup_parabolicDefiningHopfIdeal, parabolic_inf_oppositeCocharacter]

end CFSG.ThirdParty.TauCeti.Cocharacter
