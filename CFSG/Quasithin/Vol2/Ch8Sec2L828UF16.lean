module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization

public section

namespace CFSG.Quasithin.H13

open Polynomial

theorem ob5_cyc5_irred : Irreducible (cyclotomic 5 (ZMod 2)) := by
  have hn : ¬ (2 : ℕ) ∣ 5 := by norm_num
  refine ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (p := 2) hn dvd_rfl ?_
  rw [natDegree_cyclotomic]
  have : orderOf (ZMod.unitOfCoprime 2 (by norm_num : Nat.Coprime 2 5)) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨?_, fun m hm1 hm2 => ?_⟩
    · decide
    · interval_cases m <;> decide
  rw [this, Nat.totient_prime (by decide : Nat.Prime 5)]

theorem ob5_cyc5_card : Nat.card (AdjoinRoot (cyclotomic 5 (ZMod 2))) = 2 ^ 4 := by
  haveI := Fact.mk ob5_cyc5_irred
  have hf : cyclotomic 5 (ZMod 2) ≠ 0 := (cyclotomic.monic 5 (ZMod 2)).ne_zero
  have hd : (AdjoinRoot.powerBasis hf).dim = 4 := by
    rw [AdjoinRoot.powerBasis_dim, natDegree_cyclotomic,
      Nat.totient_prime (by decide : Nat.Prime 5)]
  have hfin : Module.finrank (ZMod 2) (AdjoinRoot (cyclotomic 5 (ZMod 2))) = 4 := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis hf), hd]
  haveI : Module.Finite (ZMod 2) (AdjoinRoot (cyclotomic 5 (ZMod 2))) :=
    (AdjoinRoot.powerBasis hf).finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hfin, Nat.card_zmod]

noncomputable def ob5_gfIso : AdjoinRoot (cyclotomic 5 (ZMod 2)) ≃ₐ[ZMod 2] GaloisField 2 4 := by
  haveI := Fact.mk ob5_cyc5_irred
  exact GaloisField.algEquivGaloisField 2 4 ob5_cyc5_card

noncomputable def ob5_f16Quot {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Module.End (ZMod 2) W) (hσ : aeval σ (cyclotomic 5 (ZMod 2)) = 0) :
    AdjoinRoot (cyclotomic 5 (ZMod 2)) →+* Module.End (ZMod 2) W :=
  Ideal.Quotient.lift (Ideal.span {cyclotomic 5 (ZMod 2)})
    (aeval σ : (ZMod 2)[X] →ₐ[ZMod 2] Module.End (ZMod 2) W).toRingHom (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [hσ])

noncomputable def ob5_f16Hom {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Module.End (ZMod 2) W) (hσ : aeval σ (cyclotomic 5 (ZMod 2)) = 0) :
    GaloisField 2 4 →+* Module.End (ZMod 2) W :=
  (ob5_f16Quot σ hσ).comp (ob5_gfIso.symm.toRingEquiv.toRingHom)

theorem ob5_aeval_commute {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Module.End (ZMod 2) W) (T : Module.End (ZMod 2) W) (hT : Commute T σ)
    (p : (ZMod 2)[X]) : Commute T (aeval σ p) := by
  induction p using Polynomial.induction_on with
  | C a =>
    rw [aeval_C]
    exact (Algebra.commutes a T).symm
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    exact ih.mul_right hT

theorem ob5_f16Hom_commute {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Module.End (ZMod 2) W) (hσ : aeval σ (cyclotomic 5 (ZMod 2)) = 0)
    (T : Module.End (ZMod 2) W) (hT : Commute T σ) (x : GaloisField 2 4) :
    Commute T (ob5_f16Hom σ hσ x) := by
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (ob5_gfIso.symm x)
  have hx : ob5_f16Hom σ hσ x = aeval σ p := by
    show ob5_f16Quot σ hσ (ob5_gfIso.symm x) = _
    rw [← hp]
    rfl
  rw [hx]
  exact ob5_aeval_commute σ T hT p

theorem ob5_aeval_cyc5_zero {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : Module.End (ZMod 2) W) (h5 : σ ^ 5 = 1) (hfix : ∀ w : W, σ w = w → w = 0) :
    aeval σ (cyclotomic 5 (ZMod 2)) = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [cyclotomic_prime, map_sum]
  simp only [map_pow, aeval_X]
  have hgeom : (∑ i ∈ Finset.range 5, σ ^ i) * (σ - 1) = 0 := by
    rw [geom_sum_mul, h5, sub_self]
  have hinj : Function.Injective (σ - 1 : Module.End (ZMod 2) W) := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    apply hfix w
    rw [LinearMap.sub_apply, sub_eq_zero] at hw
    exact hw
  have hsurj : Function.Surjective (σ - 1 : Module.End (ZMod 2) W) :=
    Finite.injective_iff_surjective.mp hinj
  ext w
  obtain ⟨u, rfl⟩ := hsurj w
  have := congrArg (fun T : Module.End (ZMod 2) W => T u) hgeom
  simpa [Module.End.mul_apply] using this

theorem ob5_finrank_two {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (hW : Nat.card W = 2 ^ 8) (σ : Module.End (ZMod 2) W)
    (hσ : aeval σ (cyclotomic 5 (ZMod 2)) = 0) :
    @Module.finrank (GaloisField 2 4) W _ _ (Module.compHom W (ob5_f16Hom σ hσ)) = 2 := by
  letI : Module (GaloisField 2 4) W := Module.compHom W (ob5_f16Hom σ hσ)
  have hF : Nat.card (GaloisField 2 4) = 2 ^ 4 := GaloisField.card 2 4 (by norm_num)
  have h := Module.natCard_eq_pow_finrank (K := GaloisField 2 4) (V := W)
  rw [hW, hF] at h
  have h2 : (2 : ℕ) ^ 8 = 2 ^ (4 * Module.finrank (GaloisField 2 4) W) := by
    rw [h, pow_mul]
  have := Nat.pow_right_injective (le_refl 2) h2
  omega

end CFSG.Quasithin.H13
