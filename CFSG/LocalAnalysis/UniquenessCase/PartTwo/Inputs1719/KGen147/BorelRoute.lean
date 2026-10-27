module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen147.Pair
import CFSG.RankThree.PartTwo.Sec4.RonanK432Real

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen

open Subgroup CFSG.Open
open scoped commutatorElement

theorem not_normalizer_le_normalizer_of_commutator_le {G : Type} [Group G] [Finite G]
    (hG : IsSimpleGroup G) (hna : ∃ a b : G, a * b ≠ b * a)
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 1) {B S : Subgroup G} (hB : Nat.card B = 3)
    (hS : IsPGroup 7 S) (hcomm : ⁅normalizer (S : Set G), normalizer (S : Set G)⁆ ≤ S) :
    ¬ normalizer (B : Set G) ≤ normalizer (S : Set G) := by
  intro hle
  have := hG
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 3 (by rw [hB])
  have hb3 : orderOf (b : G) = 3 := by rw [Subgroup.orderOf_coe, hb]
  have hBz : zpowers (b : G) = B := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]
      exact b.2
    · rw [hB, Nat.card_zpowers, hb3]
  obtain ⟨t, ht⟩ := CFSG.RankThree.PartTwo.Sec4.RonanK432.exists_inv_of_pRank_one hna h3 hb3
  have ht' : t⁻¹ * (b : G) * t = (b : G)⁻¹ := by
    calc t⁻¹ * (b : G) * t = t⁻¹ * (t * (b : G) * t⁻¹)⁻¹ * t := by rw [ht, inv_inv]
      _ = (b : G)⁻¹ := by group
  have htB : t ∈ normalizer (B : Set G) := by
    rw [← hBz, Subgroup.mem_normalizer_iff]
    intro y
    simp only [Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨-k, by rw [← conj_zpow, ht, inv_zpow, zpow_neg]⟩
    · rintro ⟨k, hk⟩
      refine ⟨-k, ?_⟩
      have hy : y = t⁻¹ * (b : G) ^ k * t := by rw [hk]; group
      have hconj : t⁻¹ * (b : G) ^ k * t = (t⁻¹ * (b : G) * t) ^ k := by
        simpa only [inv_inv] using (conj_zpow (a := t⁻¹) (b := (b : G)) (i := k)).symm
      rw [hy, hconj, ht', inv_zpow, zpow_neg]
  have hbS : (b : G) ∈ normalizer (S : Set G) := hle (Subgroup.le_normalizer b.2)
  have htS : t ∈ normalizer (S : Set G) := hle htB
  have hc : ⁅t, (b : G)⁆ ∈ S := hcomm (Subgroup.commutator_mem_commutator htS hbS)
  rw [commutatorElement_def, ht] at hc
  obtain ⟨k, hk⟩ := hS ⟨_, hc⟩
  have hk' : ((b : G)⁻¹ * (b : G)⁻¹) ^ 7 ^ k = 1 := congrArg Subtype.val hk
  have hpow : (b : G) ^ (2 * 7 ^ k) = 1 := by
    rw [← inv_inj, inv_one, ← hk', pow_mul, sq, ← inv_pow, mul_inv_rev]
  have hdvd : (3 : ℕ) ∣ 2 * 7 ^ k := hb3 ▸ orderOf_dvd_of_pow_eq_one hpow
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h2 | h7
  · omega
  · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h7
    omega

theorem kGenSpans_of_isCoatom_normalizer {G : Type} [Group G] [Finite G] (hG : IsSimpleGroup G)
    (hna : ∃ a b : G, a * b ≠ b * a) (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 1)
    {B R : Subgroup G} (hBR : IsKGenPair B R)
    (hS : ∃ S : Subgroup G, R ≤ S ∧ IsPGroup 7 S ∧ IsCoatom (normalizer (S : Set G)) ∧
      ⁅normalizer (S : Set G), normalizer (S : Set G)⁆ ≤ S) :
    KGenSpans B R := by
  obtain ⟨S, hRS, hS7, hco, hcomm⟩ := hS
  intro H hBH hYH
  rcases hco.le_iff.mp (hYH S hRS hS7) with hH | hH
  · exact hH
  · subst hH
    exact absurd hBH (not_normalizer_le_normalizer_of_commutator_le hG hna h3 hBR.1 hS7 hcomm)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen
