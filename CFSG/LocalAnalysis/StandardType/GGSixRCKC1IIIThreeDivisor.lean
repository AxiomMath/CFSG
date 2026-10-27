module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIField
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

public section
open scoped BigOperators
namespace CFSG.Open

theorem three_pow_three_dvd_ordBC_two {n : ℕ} (hn : 3 ≤ n) : 3 ^ 3 ∣ ordBC n 2 := by
  have hsub : Finset.Icc 1 3 ⊆ Finset.Icc 1 n := by
    intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega
  have hprod : 3 ^ 3 ∣ ∏ i ∈ Finset.Icc 1 n, (2 ^ (2 * i) - 1) :=
    (by decide +kernel : 3 ^ 3 ∣ ∏ i ∈ Finset.Icc 1 3, (2 ^ (2 * i) - 1)).trans
      (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
  simpa [ordBC] using dvd_mul_of_dvd_right hprod (2 ^ (n * n))

theorem three_pow_three_dvd_ordTwistedA_two {n : ℕ} (hn : 3 ≤ n) :
    3 ^ 3 ∣ ordTwistedA n 2 := by
  let N := 2 ^ (n * (n + 1) / 2) *
    (∏ i ∈ Finset.Icc 2 (n + 1), (2 ^ i - (-1 : ℤ) ^ i).toNat)
  have hsub : Finset.Icc 2 4 ⊆ Finset.Icc 2 (n + 1) := by
    intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega
  have h81 : 3 ^ 4 ∣ N := by
    apply dvd_mul_of_dvd_right
    exact (by decide +kernel : 3 ^ 4 ∣ ∏ i ∈ Finset.Icc 2 4, (2 ^ i - (-1 : ℤ) ^ i).toNat).trans
      (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
  have hd : Nat.gcd (n + 1) 3 ∣ 3 ^ 4 := (Nat.gcd_dvd_right (n + 1) 3).trans (by norm_num)
  have hdiv : 3 ^ 4 / Nat.gcd (n + 1) 3 ∣ N / Nat.gcd (n + 1) 3 :=
    Nat.div_dvd_div hd h81
  have h27 : 3 ^ 3 ∣ 3 ^ 4 / Nat.gcd (n + 1) 3 := by
    have h31 : Nat.gcd (n + 1) 3 = 1 ∨ Nat.gcd (n + 1) 3 = 3 := by
      exact (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp (Nat.gcd_dvd_right (n + 1) 3)
    rcases h31 with h | h <;> rw [h] <;> norm_num
  simpa [ordTwistedA, N] using h27.trans hdiv


end CFSG.Open
namespace CFSG.StandardType.RCKC1
open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos



theorem three_pow_three_dvd_card_centerQuot_of_row_III
    {X : Type} [Group X] [Finite X] {J : Subgroup X} (hrow : GGSixRCKJRow .III J) :
    3 ^ 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
  obtain ⟨lab, hlab, R, _, I, F, θ, _, _, hr, hmodel⟩ :=
    largeEvenMarking_exists_markedModel hrow
  have hm : MarkedModel lab (↥J ⧸ Subgroup.center ↥J) :=
    MarkedModel.of_mulEquiv θ.symm hmodel
  obtain ⟨hchar, hdeg, hshape⟩ := ggSixRCKLabelRow_III_parameters hlab hr
  have hm' : LieModel (↥J ⧸ Subgroup.center ↥J) (markTag lab) (markRank lab) 2 1 := by
    unfold MarkedModel at hm
    rwa [hchar, hdeg] at hm
  rcases hshape with ⟨ht, h3⟩ | ⟨ht, h4⟩
  · rw [ht] at hm'
    rw [CFSG.SeitzReduction.SymplecticPilot.card_of_lieModel_PSp_two_pow hm']
    simpa only [pow_one] using CFSG.Open.three_pow_three_dvd_ordBC_two h3
  · rw [ht] at hm'
    rw [CFSG.SeitzReduction.UnitaryPilot.card_of_lieModel_PSU_two_pow hm']
    simpa only [pow_one] using
      CFSG.Open.three_pow_three_dvd_ordTwistedA_two (by omega : 3 ≤ markRank lab - 1)


end CFSG.StandardType.RCKC1
