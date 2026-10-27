module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIField
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

public section

open scoped BigOperators

namespace CFSG.Open

theorem five_dvd_ordBC_two {n : ℕ} (hn : 2 ≤ n) : 5 ∣ ordBC n 2 := by
  have hp : 5 ∣ ∏ i ∈ Finset.Icc 1 n, (2 ^ (2 * i) - 1) := by
    exact (by norm_num : 5 ∣ 2 ^ (2 * 2) - 1).trans
      (Finset.dvd_prod_of_mem (fun i : ℕ => 2 ^ (2 * i) - 1) (by simp; omega))
  simpa [ordBC] using (dvd_mul_of_dvd_right hp (2 ^ (n * n)))

theorem five_dvd_ordTwistedA_two {n : ℕ} (hn : 3 ≤ n) : 5 ∣ ordTwistedA n 2 := by
  let N := 2 ^ (n * (n + 1) / 2) *
    (∏ i ∈ Finset.Icc 2 (n + 1), (2 ^ i - (-1 : ℤ) ^ i).toNat)
  have h5 : 5 ∣ N := by
    apply dvd_mul_of_dvd_right
    exact (by norm_num : 5 ∣ (2 ^ 4 - (-1 : ℤ) ^ 4).toNat).trans
      (Finset.dvd_prod_of_mem (fun i : ℕ => (2 ^ i - (-1 : ℤ) ^ i).toNat)
        (by simp; omega))
  have h3 : 3 ∣ N := by
    apply dvd_mul_of_dvd_right
    exact (by norm_num : 3 ∣ (2 ^ 2 - (-1 : ℤ) ^ 2).toNat).trans
      (Finset.dvd_prod_of_mem (fun i : ℕ => (2 ^ i - (-1 : ℤ) ^ i).toNat)
        (by simp; omega))
  have hd : Nat.gcd (n + 1) 3 ∣ N := (Nat.gcd_dvd_right (n + 1) 3).trans h3
  have hc : Nat.Coprime 5 (Nat.gcd (n + 1) 3) :=
    Nat.Coprime.of_dvd_right (Nat.gcd_dvd_right (n + 1) 3) (by decide)
  have h5q : 5 ∣ N / Nat.gcd (n + 1) 3 := hc.dvd_of_dvd_mul_right (by
    rw [Nat.div_mul_cancel hd]
    exact h5)
  simpa [ordTwistedA, N] using h5q

end CFSG.Open

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos




theorem five_dvd_card_centerQuot_of_row_III
    {X : Type} [Group X] [Finite X] {J : Subgroup X} (hrow : GGSixRCKJRow .III J) :
    5 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
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
    simpa only [pow_one] using CFSG.Open.five_dvd_ordBC_two (by omega : 2 ≤ markRank lab)
  · rw [ht] at hm'
    rw [CFSG.SeitzReduction.UnitaryPilot.card_of_lieModel_PSU_two_pow hm']
    simpa only [pow_one] using
      CFSG.Open.five_dvd_ordTwistedA_two (by omega : 3 ≤ markRank lab - 1)

theorem five_dvd_card_centerQuot_of_row_III_le
    {X : Type} [Group X] [Finite X] {J K : Subgroup X}
    (hrow : GGSixRCKJRow .III J) (hJK : J ≤ K) :
    5 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) :=
  (five_dvd_card_centerQuot_of_row_III hrow).trans (RCKU33.card_centerQuot_dvd hJK)

end CFSG.StandardType.RCKC1
