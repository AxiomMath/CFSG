module

import CFSG.RankThree.PartOne.SEITZ8.D4Field
import CFSG.RankThree.Chevalley.SteinbergBTTrialityCanonicalField
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.CTP.SeitzField
import CFSG.RankThree.PartOne.CTP.Spectrum

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Timmesfeld.ExceptionalOrders CFSG.Open CFSG.RankThree.PartOne.CTP

theorem prime_dvd_ordTrialityD4_two {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hd : p ∣ ordTrialityD4 2) : p = 7 ∨ p = 13 := by
  have h : ordTrialityD4 2 = 2 ^ 12 * 3 ^ 4 * 7 ^ 2 * 13 := by norm_num [ordTrialityD4]
  rw [h] at hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
        omega
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (hp.dvd_of_dvd_pow h2))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1)

variable {K : Type} [Field K]

section Orders

variable [Finite K]

theorem card_graphFixedRootGroup_D4_orient {f r : ℕ} (hf : 1 ≤ f) (hr : r = 1 ∨ r = 2)
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ ((2 ^ f) ^ r)) :
    Nat.card (graphFixedRootGroup TwistTag.D4 K σ) = ordTrialityD4 (2 ^ f) := by
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hq := card_orbitField_D4_orientation Nat.prime_two hf hK hr hσ
  have : Fintype (WeylGroup TwistTag.D4.tag) := Fintype.ofFinite _
  have hC := card_graphFixedRootGroup hsurj hq
  rw [sum_length_relWeylTwist_D4, ncard_posRoots_twistedD4] at hC
  have hodd : Odd (Nat.card K - 1) := by
    rw [hK, ← pow_mul]
    exact Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  have hT := card_compatTorus_mul (t := TwistTag.D4) (K := K) σ
  rw [card_compat_inf_ker_D4 σ hodd, card_compatSubgroup, mul_one] at hT
  simp only [hq] at hT
  rw [prod_orbit_D4] at hT
  rw [hC, hT, ← ordTrialityD4_eq _ Nat.one_le_two_pow]

theorem card_fixedSubgroup_two {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Nat.card K = 2 ^ (3 * 1 * p)) {σ δ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ (1 * p))
    (hδ : ∀ c, δ c = c ^ 2 ^ (3 * 1)) :
    Nat.card (fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)) = ordTrialityD4 2 := by
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  obtain ⟨-, -, hk, -, -, -, hfixJ, -⟩ :=
    CFSG.RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel
      Nat.prime_two (le_refl 1) hp.two_le hm3 K hK σ hσ δ hδ
  have e3 : ↥(fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)) ≃*
      ↥(trialityFieldImage σ δ) :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
      (MulEquiv.subgroupCongr hfixJ)
  have e4 : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
      (fixSubfieldRestrict σ δ).toRingHom) ≃* ↥(trialityFieldImage σ δ) :=
    Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective (fixSubfield δ).subtype)
  have hj : p % 3 = 1 ∨ p % 3 = 2 := by
    have h0 : p % 3 ≠ 0 := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.dvd_of_mod_eq_zero h)
      omega
    omega
  rw [Nat.card_congr e3.toEquiv, ← Nat.card_congr e4.toEquiv]
  have := card_graphFixedRootGroup_D4_orient (K := fixSubfield δ) (f := 1) (r := p % 3)
    (le_refl 1) hj (by rw [hk]; norm_num) (fixSubfieldRestrict σ δ).toRingHom (fun c => by
      apply Subtype.ext
      show σ (c : K) = ((c ^ (2 ^ 1) ^ (p % 3) : fixSubfield δ) : K)
      rw [hσ, SubmonoidClass.coe_pow]
      exact sigma_pow_on_fix (f0 := 1) (p := p) hk c.2)
  rw [this]
  norm_num

end Orders

end CFSG.RankThree.PartOne.SEITZ8
