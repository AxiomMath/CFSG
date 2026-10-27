module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalTwisted
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalizedStatements
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.TwistedOrders
import CFSG.RankThree.Classical2.TwistedE6RationalOrder

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic
  finite_field_automorphism_fixed_field_cardinality)
open CFSG.RankThree.Chevalley (subfieldRootGroupImage
  twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer)
open CFSG.RankThree.Classical2 (twisted_E6_full_rational_fixed_group_order)
open CFSG.Timmesfeld.ExceptionalOrders (card_orbitField card_graphFixedPosUnipotent
  ncard_posRoots_twistedE6)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem prime_dvd_card_graphFixedRootGroup_E6
    {ℓ f s : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hs : s.Prime) (hs3 : s ≠ 3)
    (hdvd : s ∣ (ℓ ^ f) ^ 36 * ((ℓ ^ f) ^ 12 - 1) * ((ℓ ^ f) ^ 9 + 1) * ((ℓ ^ f) ^ 8 - 1) *
      ((ℓ ^ f) ^ 6 - 1) * ((ℓ ^ f) ^ 5 + 1) * ((ℓ ^ f) ^ 2 - 1)) :
    s ∣ Nat.card (graphFixedRootGroup TwistTag.E6 K σ) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (by omega : 1 ≤ f * 2)
    (by rw [hK, ← pow_mul])
  let Ω := AlgebraicClosure K
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  obtain ⟨hfin, -, hder, ⟨k, hk⟩, -, hRcard, -⟩ := twisted_E6_full_rational_fixed_group_order hℓ hf
    K hK σ hσ Ω (iterateFrobenius Ω ℓ f) (fun c => iterateFrobenius_def ℓ f c)
  set H := (graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL (algebraMap K Ω)) with hH
  set R := twistedFixedGroup TwistTag.E6 Ω (iterateFrobenius Ω ℓ f) with hR
  have hle : H ≤ R := by
    rw [← hder]
    exact Subgroup.commutator_le_self _
  have hcardH : Nat.card H = Nat.card (graphFixedRootGroup TwistTag.E6 K σ) :=
    Subgroup.card_map_of_injective (baseChangeGL_injective _)
  have hmul := Subgroup.card_mul_index (H.subgroupOf R)
  rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcardH, hRcard] at hmul
  have hcop : Nat.Coprime s (3 ^ k) :=
    ((Nat.coprime_primes hs Nat.prime_three).2 hs3).pow_right k
  have hsd : s ∣ Nat.card (graphFixedRootGroup TwistTag.E6 K σ) * 3 ^ k := by
    rw [hmul]
    exact hdvd
  exact hcop.dvd_of_dvd_mul_right hsd

theorem pow_dvd_card_graphFixedRootGroup_E6
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    ℓ ^ (36 * f) ∣ Nat.card (graphFixedRootGroup TwistTag.E6 K σ) := by
  have hsurj : Function.Surjective σ := by
    have := Finite.surjective_of_injective σ.injective
    exact this
  have hq := card_orbitField (t := TwistTag.E6) hℓ hf hK hσ
  have hU := card_graphFixedPosUnipotent hsurj hq
  rw [ncard_posRoots_twistedE6] at hU
  have hle : graphFixedPosUnipotent TwistTag.E6 K σ ≤ graphFixedRootGroup TwistTag.E6 K σ :=
    graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hU, ← pow_mul, mul_comm f 36] at hdvd
  exact hdvd

theorem nonLocalized_twistedE6_of_ne
    {ℓ d p : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) (hp : p.Prime)
    (hp3 : 3 < p) (hne : ¬ ((ℓ = 2 ∨ ℓ = 3) ∧ d = 1)) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ (2 * d * p)) (κ σ : K ≃+* K) (σ₀ : fixSubfield κ ≃+* fixSubfield κ)
    (hκ : ∀ c, κ c = c ^ ℓ ^ (2 * d)) (hσ : ∀ c, σ c = c ^ ℓ ^ (d * p))
    (hσ₀ : ∀ c, (σ₀ c : K) = (c : K) ^ ℓ ^ d) :
    NonLocalized ((subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) := by
  classical
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ
    (Nat.mul_pos (Nat.mul_pos (by norm_num) hd) hp.pos) hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨fr, hfr, -⟩ := finite_field_automorphism_fixed_field_cardinality hℓ
    (Nat.mul_pos (Nat.mul_pos (by norm_num) hd) hp.pos) hK
  obtain ⟨ε, hε⟩ : ∃ ε : K ≃+* K, ∀ c, ε c = c ^ ℓ ^ (d * (p + 1)) :=
    ⟨fr ^ (d * (p + 1)), fun c => ringAut_pow_apply_of_frobenius hfr (d * (p + 1)) c⟩
  obtain ⟨-, hk, hJC, -, -, hsJ, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer hℓ hd
      (by omega : 3 ≤ p) hpodd K hK κ hκ σ hσ σ₀ hσ₀ ε hε
  have : Finite (fixSubfield κ) := Subtype.finite
  set C := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hCdef
  set J := subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀ with hJdef
  have hk2 : Nat.card (fixSubfield κ) = (ℓ ^ d) ^ 2 := by rw [hk, ← pow_mul, mul_comm]
  have hσ₀k : ∀ c : fixSubfield κ, σ₀.toRingHom c = c ^ (ℓ ^ d) := fun c =>
    Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hσ₀ c)
  have hcardJ : Nat.card (J.subgroupOf C) = Nat.card (graphFixedRootGroup TwistTag.E6
      (fixSubfield κ) σ₀.toRingHom) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJC).toEquiv).trans
      (Nat.card_congr (Equiv.symm ((graphFixedRootGroup TwistTag.E6 (fixSubfield κ)
        σ₀.toRingHom).equivMapOfInjective
          (baseChangeGL (τ := TwistTag.E6.tag) (fixSubfield κ).subtype)
          (baseChangeGL_injective _)).toEquiv))
  have hR : ∃ R : Subgroup C, R ≤ J.subgroupOf C ∧ ¬ Nat.card R ∣ (78).factorial := by
    refine exists_le_subgroup_card_not_dvd_factorial (J := J.subgroupOf C) ?_
    by_cases h22 : ℓ = 2 ∧ d = 2
    · obtain ⟨rfl, rfl⟩ := h22
      refine exists_subgroup_card_not_dvd_factorial (s := 257) (e := 1) hcardJ (by norm_num)
        ?_ ?_
      · rw [pow_one]
        exact prime_dvd_card_graphFixedRootGroup_E6 hℓ hd (fixSubfield κ) hk2 σ₀.toRingHom
          hσ₀k (by norm_num) (by norm_num) (by decide)
      · rw [pow_one]
        exact not_dvd_factorial_of_lt (by norm_num) (by norm_num)
    · refine exists_subgroup_card_not_dvd_factorial (s := ℓ) (e := 36 * d) hcardJ hℓ
        (pow_dvd_card_graphFixedRootGroup_E6 hℓ hd (fixSubfield κ) hk2 σ₀.toRingHom hσ₀k)
        (not_pow_dvd_factorial_seventyeight hℓ hd (fun h2 => ?_) (fun h3 => ?_))
      · by_contra h
        have hd2 : d = 1 ∨ d = 2 := by omega
        rcases hd2 with h1 | h1
        · exact hne ⟨Or.inl h2, h1⟩
        · exact h22 ⟨h2, h1⟩
      · by_contra h
        exact hne ⟨Or.inr h3, by omega⟩
  obtain ⟨R, hRJ, hR⟩ := hR
  have h78 : TwistTag.E6.tag.rank + TwistTag.E6.tag.rootCount = 78 := by decide
  have hsimple : IsSimpleGroup (J.subgroupOf C) :=
    (Subgroup.subgroupOfEquivOfLe hJC).isSimpleGroup
  have hσι : ∀ c : fixSubfield κ, σ.toRingHom ((fixSubfield κ).subtype c) =
      (fixSubfield κ).subtype (σ₀.toRingHom c) := fun c => by
    have hpe : d * p = 2 * d * (p / 2) + d := by
      have h2 := Nat.div_add_mod p 2
      have h3 : p % 2 = 1 := Nat.odd_iff.1 hpodd
      nlinarith [h2, h3]
    have h1 := pow_pow_add_mul_eq (ℓ := ℓ) (m := 2 * d) (k := fixSubfield κ) hk (p / 2) d c
    rw [← hpe] at h1
    have h2 := congrArg Subtype.val h1
    rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow] at h2
    change σ (c : K) = ((σ₀ c : fixSubfield κ) : K)
    rw [hσ, hσ₀]
    exact h2
  exact nonLocalized_twisted_of_simple TwistTag.E6 ℓ (fixSubfield κ).subtype σ.toRingHom
    σ₀.toRingHom σ₀.surjective hσι hsimple R hRJ (by rw [h78]; exact hR)

theorem subfieldNonLocalizedTwistedE6_of
    (h : SubfieldNonLocalizedTwistedE6Small) :
    SubfieldNonLocalizedTwistedE6 := by
  intro ℓ d p hℓ hd hp hp3 K _ _ hK κ σ σ₀ hκ hσ hσ₀
  by_cases hsmall : (ℓ = 2 ∨ ℓ = 3) ∧ d = 1
  · exact h ℓ d p hℓ hd hp hp3 hsmall.1 hsmall.2 K hK κ σ σ₀ hκ hσ hσ₀
  · exact nonLocalized_twistedE6_of_ne hℓ hd hp hp3 hsmall K hK κ σ σ₀ hκ hσ hσ₀

end CFSG.SignalizerFunctorTheorem.CatalogBridge
