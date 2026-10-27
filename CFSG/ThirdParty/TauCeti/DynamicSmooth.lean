/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import CFSG.ThirdParty.TauCeti.DynamicRepresentability
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat

/-!
# Smoothness of dynamic parabolic subgroups

This file is adapted from the TauCeti repository at `main` commit
`6fee5c0a9fb3444eb4aa6a4a6248c33258a11d5c`, file
`TauCeti/Algebra/AlgebraicGroup/Dynamic/Smooth.lean`. The CFSG dependency pin
`6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380` predates these results. The declarations are
reproduced in the `CFSG.ThirdParty.TauCeti` namespace with unchanged statements, so that a
later TauCeti bump does not clash with the upstream names; references to declarations that
already exist at the pin point at those pinned declarations.

Let `λ : 𝔾ₘ → G` be a cocharacter of an affine group `G = Spec H`, with dynamic parabolic
`P(λ)`. This file proves that `P(λ)` is formally smooth whenever `G` is, over an arbitrary
commutative base ring, and hence that `P(λ)` is smooth when `G` is a smooth affine group of
finite type over a Noetherian ring.

The proof is the infinitesimal lifting criterion. Let `C → C ⧸ J` be a square-zero thickening
and `g₀ ∈ P(λ)(C ⧸ J)`. By definition `T ↦ λ(T) g₀ λ(T)⁻¹` extends to a point `F₀` over
`(C ⧸ J)[X]`, and smoothness of `G` lifts `F₀` to some point `F` over `C[X]`. The lift `F` need
not be equivariant, so `F(1)` need not lie in `P(λ)(C)`. The point `Ψ = λ(T)⁻¹ F λ(T)` over
`C[T;T⁻¹]` reduces to the constant point `g₀` modulo `J`, and the constant coefficient of `Ψ` is
the required lift. It is multiplicative because the nonconstant coefficients of `Ψ` lie in the
square-zero ideal `J`. It lies in `P(λ)(C)` because on a coefficient `x` of weight `n` of
universal conjugation, `Ψ` is `F(x) · T⁻ⁿ`, whose constant coefficient is the `Xⁿ`-coefficient
of `F(x)`. That coefficient vanishes for `n < 0`.

The source files and their main declarations are:

* `TauCeti/Algebra/AlgebraicGroup/Dynamic/Smooth.lean`:
  `CFSG.ThirdParty.TauCeti.BialgHom.formallySmooth_quotient_parabolicDefiningHopfIdeal` and
  `CFSG.ThirdParty.TauCeti.BialgHom.smoothCommHopfAlgProperty_quotient_parabolicDefiningHopfIdeal`;
  the upstream private helpers `twistedPoint`, `twistedPoint_coeff_conjugationAlgHom`,
  `mapValue_twistedPoint`, `mk_coeff_of_mapValue_eq_constPoint`, `constCoeffAlgHom`,
  `constCoeffAlgHom_apply` and `mkₐ_comp_constCoeffAlgHom`, made public here;
* `TauCeti/Algebra/Polynomial/Laurent/Coeff.lean`:
  `CFSG.ThirdParty.TauCeti.LaurentPolynomial.coeff_T_mul` and
  `CFSG.ThirdParty.TauCeti.LaurentPolynomial.mul_coeff_zero_of_coeff_mem`.

The unipotent and Levi smoothness theorems of the source file are not ported; only the
parabolic statements are in scope here.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1 (Proposition 2.1.8(1)).

## Adaptations to the pinned API

* Every ported declaration is placed in a namespace rooted at `CFSG.ThirdParty.TauCeti`;
  references to ported declarations are correspondingly qualified.
* The cocharacter conjugation algebra map `conjugationAlgHom`, its coefficient formula
  `coeff_conjugate`, the defining Hopf ideal `parabolicDefiningHopfIdeal` and the membership
  lemmas `parabolicDefiningHopfIdeal_toIdeal` and
  `coeff_conjugationAlgHom_mem_parabolicDefiningHopfIdeal`, together with
  `exists_algHom_toLaurent_comp_eq_iff` and `exists_toLaurent_eq_iff`, are the ported
  declarations of `CFSG/ThirdParty/TauCeti/DynamicRepresentability.lean`; the point
  constructions `genericPoint`, `ofPolyPoint`, `constPoint`, `conjugate` and their
  `mapValue` naturality lemmas are the pinned TauCeti declarations.
* The pinned `TauCeti.MultiplicativeGroup.genericUnit` and
  `TauCeti.MultiplicativeGroup.genericUnit_zpow_val` replace the new
  `LaurentPolynomial.genericUnit` and `LaurentPolynomial.genericUnit_zpow_val` used by the
  source file, which the pin predates.
* The pinned `TauCeti.laurentEval` and its lemmas `laurentEval_C` and `laurentEval_T` are
  reused in place of the source file's copies.
* The source file imports `TauCeti.Algebra.Polynomial.Laurent.Coeff`, which the pin does not
  have; the two lemmas of that file used by the proof below are ported here.
* The upstream private helpers are made public with docstrings. The two public definitions
  `twistedPoint` and `constCoeffAlgHom` are marked `@[expose]`, since the proofs of their
  equation lemmas in this module unfold their bodies.
* The quotient object `FiniteTypeCommHopfAlgCat.quotient` is the pinned declaration.
-/

public section

open CategoryTheory WithConv TauCeti
open _root_.TauCeti.Cocharacter
open CFSG.ThirdParty.TauCeti.Cocharacter

namespace CFSG.ThirdParty.TauCeti

namespace LaurentPolynomial

variable {R : Type*} [Semiring R]

/-- Left multiplication by `T n` shifts coefficients by `n`. This is not a `simp` lemma: `simp`
moves `T n` to the right with `LaurentPolynomial.T_mul`. -/
theorem coeff_T_mul (n : ℤ) (f : _root_.LaurentPolynomial R) (d : ℤ) :
    (_root_.LaurentPolynomial.T n * f).coeff d = f.coeff (d - n) := by
  simpa only [_root_.LaurentPolynomial.T, one_mul, sub_eq_add_neg, add_comm] using
    AddMonoidAlgebra.coeff_single_mul_apply f (1 : R) n d

/-- If all nonconstant coefficients of two Laurent polynomials lie in a square-zero ideal, the
constant coefficient of their product is the product of their constant coefficients. Thus the
constant coefficient is a ring homomorphism on the Laurent polynomials that are constant modulo
such an ideal. -/
theorem mul_coeff_zero_of_coeff_mem {R : Type*} [CommSemiring R] {I : Ideal R} (hI : I ^ 2 = ⊥)
    {f g : _root_.LaurentPolynomial R} (hf : ∀ n ≠ 0, f.coeff n ∈ I)
    (hg : ∀ n ≠ 0, g.coeff n ∈ I) :
    (f * g).coeff 0 = f.coeff 0 * g.coeff 0 := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_eq_single 0]
  · simp
  · intro n _ hn
    have hmem : f.coeff n * g.coeff (-n + 0) ∈ I ^ 2 :=
      pow_two I ▸ Ideal.mul_mem_mul (hf n hn) (hg _ (by simpa using hn))
    simpa [hI] using hmem
  · simp

end LaurentPolynomial

namespace BialgHom

universe u v

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]

section Lift

variable {C : Type*} [CommRing C] [Algebra R C] (l : H →ₐc[R] _root_.LaurentPolynomial R)

/-- The point `l(T)⁻¹ · F · l(T)` over `C[T;T⁻¹]` obtained from a point `F` over `C[X]`. -/
@[expose]
noncomputable def twistedPoint (F : WithConv (H →ₐ[R] Polynomial C)) :
    WithConv (H →ₐ[R] _root_.LaurentPolynomial C) :=
  (genericPoint C l)⁻¹ * ofPolyPoint C F * genericPoint C l

/-- On a coefficient of weight `n` of universal conjugation, the twisted point is the value of
`F`, read as a Laurent polynomial, times `T⁻ⁿ`. -/
theorem twistedPoint_coeff_conjugationAlgHom (F : WithConv (H →ₐ[R] Polynomial C))
    (h : H) (n : ℤ) :
    (twistedPoint l F).ofConv ((conjugationAlgHom l h).coeff n) =
      (F.ofConv ((conjugationAlgHom l h).coeff n)).toLaurent * _root_.LaurentPolynomial.T (-n) := by
  -- The twisted point is generic conjugation of `F` followed by the substitution `T' ↦ T⁻¹`.
  let ψ : _root_.LaurentPolynomial (_root_.LaurentPolynomial C) →ₐ[R] _root_.LaurentPolynomial C :=
    (laurentEval (R := _root_.LaurentPolynomial C)
      (MultiplicativeGroup.genericUnit C)⁻¹).restrictScalars R
  have hψ : AlgHom.mapValue ψ (conjugate (_root_.LaurentPolynomial C) l (ofPolyPoint C F)) =
      twistedPoint l F := by
    have hu : Units.map ψ.toMonoidHom
        (MultiplicativeGroup.genericUnit (_root_.LaurentPolynomial C)) =
        (MultiplicativeGroup.genericUnit C)⁻¹ :=
      Units.ext (by simp [ψ])
    have hc : ψ.comp (IsScalarTower.toAlgHom R (_root_.LaurentPolynomial C)
        (_root_.LaurentPolynomial (_root_.LaurentPolynomial C))) = AlgHom.id R _ :=
      AlgHom.ext fun p ↦ by simp [ψ]
    rw [mapValue_conjugate, hu, hc, AlgHom.mapValue_id, MonoidHom.id_apply, map_inv, inv_inv,
      ← genericPoint_eq_pointsHom, twistedPoint]
  rw [← hψ, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
    conjugate_ofConv_coeff_conjugationAlgHom, map_mul]
  simp only [ψ, ofPolyPoint_apply, ofConv_toConv, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Polynomial.toLaurentAlg_apply, laurentEval_C, Algebra.algebraMap_self, RingHom.id_apply,
    laurentEval_T, inv_zpow', MultiplicativeGroup.genericUnit_zpow_val]

/-- If `F` reduces, along `φ`, to the extension over the affine line of the conjugation family of
`g₀`, then the twisted point reduces to the constant point `g₀`. -/
theorem mapValue_twistedPoint {D : Type*} [CommRing D] [Algebra R D] (φ : C →ₐ[R] D)
    (F : WithConv (H →ₐ[R] Polynomial C)) (g₀ : WithConv (H →ₐ[R] D))
    (hF : ofPolyPoint D (AlgHom.mapValue (Polynomial.mapAlgHom φ) F) = conjugate D l g₀) :
    AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ φ) (twistedPoint l F) = constPoint D g₀ := by
  rw [twistedPoint, map_mul, map_mul, map_inv, mapValue_genericPoint, mapValue_ofPolyPoint, hF,
    conjugate_apply]
  group

section ConstCoeff

variable {J : Ideal C} {Ψ : WithConv (H →ₐ[R] _root_.LaurentPolynomial C)}
  {g₀ : WithConv (H →ₐ[R] C ⧸ J)}

/-- If `Ψ` reduces modulo `J` to the constant point `g₀`, then its coefficients reduce to those
of `g₀`. -/
theorem mk_coeff_of_mapValue_eq_constPoint
    (hΨ : AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ (Ideal.Quotient.mkₐ R J)) Ψ =
      constPoint (C ⧸ J) g₀) (h : H) (n : ℤ) :
    Ideal.Quotient.mk J ((Ψ.ofConv h).coeff n) = if n = 0 then g₀.ofConv h else 0 := by
  have := congrArg (fun x : WithConv (H →ₐ[R] _root_.LaurentPolynomial (C ⧸ J)) ↦
    (x.ofConv h).coeff n) hΨ
  simpa [constPoint_apply, _root_.LaurentPolynomial.C_apply] using this

/-- The constant coefficient of a point `Ψ` over `C[T;T⁻¹]` that reduces, modulo a square-zero
ideal `J`, to a constant point. It is an algebra map because the nonconstant coefficients of `Ψ`
lie in `J`. -/
@[expose]
noncomputable def constCoeffAlgHom (hJ : J ^ 2 = ⊥)
    (hΨ : AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ (Ideal.Quotient.mkₐ R J)) Ψ =
      constPoint (C ⧸ J) g₀) : H →ₐ[R] C where
  toFun h := (Ψ.ofConv h).coeff 0
  map_one' := by simp
  map_mul' a b := by
    have hmem (h : H) (n : ℤ) (hn : n ≠ 0) : (Ψ.ofConv h).coeff n ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, mk_coeff_of_mapValue_eq_constPoint hΨ]
      simp [hn]
    rw [map_mul]
    exact CFSG.ThirdParty.TauCeti.LaurentPolynomial.mul_coeff_zero_of_coeff_mem hJ (hmem a) (hmem b)
  map_zero' := by simp
  map_add' a b := by simp
  commutes' r := by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R C (_root_.LaurentPolynomial C),
      ← _root_.LaurentPolynomial.C_eq_algebraMap, _root_.LaurentPolynomial.C_apply]
    simp

/-- The constant coefficient map of `constCoeffAlgHom` is evaluation at the constant
coefficient. -/
theorem constCoeffAlgHom_apply (hJ : J ^ 2 = ⊥)
    (hΨ : AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ (Ideal.Quotient.mkₐ R J)) Ψ =
      constPoint (C ⧸ J) g₀) (h : H) :
    constCoeffAlgHom hJ hΨ h = (Ψ.ofConv h).coeff 0 :=
  rfl

/-- The constant coefficient of `Ψ` lifts `g₀`. -/
theorem mkₐ_comp_constCoeffAlgHom (hJ : J ^ 2 = ⊥)
    (hΨ : AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ (Ideal.Quotient.mkₐ R J)) Ψ =
      constPoint (C ⧸ J) g₀) :
    (Ideal.Quotient.mkₐ R J).comp (constCoeffAlgHom hJ hΨ) = g₀.ofConv := by
  refine AlgHom.ext fun h ↦ ?_
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, constCoeffAlgHom_apply,
    mk_coeff_of_mapValue_eq_constPoint hΨ]
  simp

end ConstCoeff

end Lift

/-- **The dynamic parabolic of a formally smooth affine group is formally smooth.** No
finite-type, field or reductivity hypothesis is needed. -/
instance formallySmooth_quotient_parabolicDefiningHopfIdeal
    (l : H →ₐc[R] _root_.LaurentPolynomial R) [Algebra.FormallySmooth R H] :
    Algebra.FormallySmooth R (H ⧸ (parabolicDefiningHopfIdeal l).toIdeal) := by
  refine Algebra.FormallySmooth.iff_comp_surjective.mpr fun C _ _ J hJ f ↦ ?_
  -- The point `g₀` of `P(l)(C ⧸ J)` given by `f`, and its extension `F₀` over the affine line.
  let g₀ : WithConv (H →ₐ[R] C ⧸ J) := toConv (f.comp (Ideal.Quotient.mkₐ R _))
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : H →ₐ[R] Polynomial (C ⧸ J),
      (Polynomial.toLaurentAlg.restrictScalars R).comp F₀ = (conjugate (C ⧸ J) l g₀).ofConv := by
    refine exists_algHom_toLaurent_comp_eq_iff.mpr fun h n hn ↦ ?_
    have hI : (conjugationAlgHom l h).coeff n ∈ (parabolicDefiningHopfIdeal l).toIdeal :=
      HopfIdeal.mem_toIdeal.mpr (coeff_conjugationAlgHom_mem_parabolicDefiningHopfIdeal l h hn)
    rw [coeff_conjugate]
    simp [g₀, Ideal.Quotient.eq_zero_iff_mem.mpr hI]
  -- Lift `F₀` along the square-zero thickening `C[X] → (C ⧸ J)[X]`.
  let π := Polynomial.mapAlgHom (Ideal.Quotient.mkₐ R J)
  have hπ : Function.Surjective π := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : IsNilpotent (RingHom.ker (π : Polynomial C →+* Polynomial (C ⧸ J))) := by
    refine ⟨2, ?_⟩
    simp only [π, Polynomial.toRingHom_mapAlgHom]
    rw [Polynomial.ker_mapRingHom, Ideal.Quotient.mkₐ_ker, ← Ideal.map_pow, hJ, Ideal.map_bot,
      Ideal.zero_eq_bot]
  let F := Algebra.FormallySmooth.liftOfSurjective F₀ π hπ hker
  have hF : π.comp F = F₀ := Algebra.FormallySmooth.comp_liftOfSurjective F₀ π hπ hker
  -- The twisted point `Ψ = l(T)⁻¹ · F · l(T)` reduces modulo `J` to the constant point `g₀`.
  let Ψ := twistedPoint l (toConv F)
  have hΨ : AlgHom.mapValue (AddMonoidAlgebra.mapAlgHom ℤ (Ideal.Quotient.mkₐ R J)) Ψ =
      constPoint (C ⧸ J) g₀ := by
    refine mapValue_twistedPoint l _ _ g₀ ?_
    rw [AlgHom.mapValue_apply, ofConv_toConv, hF, ofPolyPoint_apply, ofConv_toConv, hF₀,
      toConv_ofConv]
  -- Its constant coefficient is an algebra map lifting `g₀`.
  let g := constCoeffAlgHom hJ hΨ
  -- It vanishes on the negative coefficients of universal conjugation, which generate the
  -- defining ideal of the dynamic parabolic.
  have hgI : (parabolicDefiningHopfIdeal l).toIdeal ≤ RingHom.ker g := by
    rw [parabolicDefiningHopfIdeal_toIdeal, Ideal.span_le]
    rintro _ ⟨h, n, hn, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, constCoeffAlgHom_apply,
      twistedPoint_coeff_conjugationAlgHom, ← _root_.LaurentPolynomial.T_mul,
      CFSG.ThirdParty.TauCeti.LaurentPolynomial.coeff_T_mul, zero_sub, neg_neg]
    exact exists_toLaurent_eq_iff.mp ⟨_, rfl⟩ n hn
  refine ⟨Ideal.Quotient.liftₐ _ g fun x hx ↦ RingHom.mem_ker.mp (hgI hx),
    Ideal.Quotient.algHom_ext R ?_⟩
  rw [AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp, mkₐ_comp_constCoeffAlgHom]

section FiniteType

variable [IsNoetherianRing R] {H : FiniteTypeCommHopfAlgCat.{u, v} R}

/-- **The dynamic parabolic of a smooth affine group of finite type over a Noetherian ring is
smooth.** -/
theorem smoothCommHopfAlgProperty_quotient_parabolicDefiningHopfIdeal
    [Algebra.Smooth R H] (l : H →ₐc[R] _root_.LaurentPolynomial R) :
    smoothCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient H (parabolicDefiningHopfIdeal l)).obj := by
  rw [smoothCommHopfAlgProperty_iff]
  exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

end FiniteType

end BialgHom

end CFSG.ThirdParty.TauCeti
