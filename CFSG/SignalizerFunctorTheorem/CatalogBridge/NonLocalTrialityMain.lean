module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalTwisted
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalizedStatements
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.TwistedOrders
import CFSG.RankThree.Chevalley.SteinbergBTTrialityCanonicalField

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley (triality_canonical_field_full_centralizer_and_pointwise_kernel)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem nonLocalized_triality_of_ne
    {ℓ d p : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) (hp : p.Prime)
    (hp3 : 3 < p) (hne : ¬ (ℓ = 2 ∧ d = 1)) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ (3 * d * p)) (σ δ : K ≃+* K) (hσ : ∀ c, σ c = c ^ ℓ ^ (d * p))
    (hδ : ∀ c, δ c = c ^ ℓ ^ (3 * d)) :
    NonLocalized ((trialityFieldImage σ δ).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  classical
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  obtain ⟨-, -, hk, -, -, hJC, -, hsJ, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel hℓ hd hp.two_le hm3 K hK σ hσ δ
      hδ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ
    (Nat.mul_pos (Nat.mul_pos (by norm_num) hd) hp.pos) hK
  have : Finite (fixSubfield δ) := Subtype.finite
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hCdef
  set J := trialityFieldImage σ δ with hJdef
  have hk3 : Nat.card (fixSubfield δ) = (ℓ ^ d) ^ 3 := by rw [hk, ← pow_mul, mul_comm]
  obtain ⟨r, hr, hσr⟩ : ∃ r : ℕ, (r = 1 ∨ r = 2) ∧
      ∀ c : fixSubfield δ, (fixSubfieldRestrict σ δ).toRingHom c = c ^ ((ℓ ^ d) ^ r) := by
    have hp3' : p % 3 = 1 ∨ p % 3 = 2 := by
      have h3 : ¬ 3 ∣ p := fun h => by
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h
        omega
      omega
    refine ⟨p % 3, hp3', fun c => ?_⟩
    apply Subtype.ext
    have hpe : d * p = 3 * d * (p / 3) + d * (p % 3) := by
      have := Nat.div_add_mod p 3
      nlinarith [this]
    have h1 := pow_pow_add_mul_eq (ℓ := ℓ) (m := 3 * d) (k := fixSubfield δ) hk (p / 3)
      (d * (p % 3)) c
    rw [← hpe] at h1
    change σ (c : K) = ((c ^ ((ℓ ^ d) ^ (p % 3)) : fixSubfield δ) : K)
    rw [hσ, SubmonoidClass.coe_pow, ← pow_mul]
    have h2 := congrArg Subtype.val h1
    rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow] at h2
    exact h2
  have hcard := (triality_both_orientations_exact_finite_order ℓ d hℓ hd (fixSubfield δ) hk3 r hr
    (fixSubfieldRestrict σ δ).toRingHom hσr).1
  have hcardJ : Nat.card (J.subgroupOf C) = Nat.card (graphFixedRootGroup TwistTag.D4
      (fixSubfield δ) (fixSubfieldRestrict σ δ).toRingHom) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJC).toEquiv).trans
      (Nat.card_congr (Equiv.symm ((graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
        (fixSubfieldRestrict σ δ).toRingHom).equivMapOfInjective
          (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield δ).subtype)
          (baseChangeGL_injective _)).toEquiv))
  obtain ⟨s, e, hs, hdvd, hnd⟩ := exists_prime_pow_dvd_not_dvd_factorial_D4 hℓ hd hne
  obtain ⟨R, hRJ, hR⟩ := exists_le_subgroup_card_not_dvd_factorial
    (J := J.subgroupOf C) (n := 28)
    (exists_subgroup_card_not_dvd_factorial (hcardJ.trans hcard) hs hdvd hnd)
  have h28 : TwistTag.D4.tag.rank + TwistTag.D4.tag.rootCount = 28 := by decide
  have hsimple : IsSimpleGroup (J.subgroupOf C) :=
    (Subgroup.subgroupOfEquivOfLe hJC).isSimpleGroup
  exact nonLocalized_twisted_of_simple TwistTag.D4 ℓ (fixSubfield δ).subtype σ.toRingHom
    (fixSubfieldRestrict σ δ).toRingHom (fixSubfieldRestrict σ δ).surjective
    (fun c => (coe_fixSubfieldRestrict σ δ c).symm) hsimple R hRJ (by rw [h28]; exact hR)

theorem subfieldNonLocalizedTriality_of
    (h : SubfieldNonLocalizedTrialityTwo) :
    SubfieldNonLocalizedTriality := by
  intro ℓ d p hℓ hd hp hp3 K _ _ hK σ δ hσ hδ
  by_cases h21 : ℓ = 2 ∧ d = 1
  · obtain ⟨rfl, rfl⟩ := h21
    exact h p hp hp3 K (by simpa using hK) σ δ (by simpa using hσ) (by simpa using hδ)
  · exact nonLocalized_triality_of_ne hℓ hd hp hp3 h21 K hK σ δ hσ hδ

end CFSG.SignalizerFunctorTheorem.CatalogBridge
