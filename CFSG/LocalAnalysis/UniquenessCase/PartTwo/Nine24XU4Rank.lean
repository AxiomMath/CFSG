module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviU4Model
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
open CFSG.ClassicalGroups.UnitaryFlag

private theorem n924x_three_dvd_two_pow_sub_one {n : ℕ} (hn : Even n) : 3 ∣ 2 ^ n - 1 := by
  obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp hn
  have hpow : 2 ^ (2 * k) = 4 ^ k := by rw [pow_mul]; norm_num
  have h4 : 4 ^ k ≡ 1 [MOD 3] := by
    simpa using (show (4 : ℕ) ≡ 1 [MOD 3] by decide).pow k
  have h : 2 ^ (2 * k) ≡ 1 [MOD 3] := by rw [hpow]; exact h4
  exact (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mp h.symm

private theorem n924x_three_dvd_two_pow_add_one {n : ℕ} (hn : Odd n) : 3 ∣ 2 ^ n + 1 := by
  obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp hn
  have hpow : 2 ^ (2 * k) = 4 ^ k := by rw [pow_mul]; norm_num
  have h4 : 4 ^ k ≡ 1 [MOD 3] := by
    simpa using (show (4 : ℕ) ≡ 1 [MOD 3] by decide).pow k
  have h2 : 2 ^ (2 * k + 1) ≡ 2 [MOD 3] := by
    rw [pow_succ, hpow]
    simpa using h4.mul (show (2 : ℕ) ≡ 2 [MOD 3] from rfl)
  have h3 : 2 ^ (2 * k + 1) + 1 ≡ 0 [MOD 3] :=
    (h2.add (show (1 : ℕ) ≡ 1 [MOD 3] from rfl)).trans
      (by decide : (2 + 1) ≡ 0 [MOD 3])
  exact Nat.modEq_zero_iff_dvd.mp h3

theorem two_le_pRank_three_of_isU4 {U : Type} [Group U] [Finite U] {n : ℕ} (hn : 2 ≤ n)
    (hU : IsU4 U n) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup U) := by
  obtain ⟨K, hK, h, ⟨e⟩⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hU
  letI : Field K := hK
  haveI : Finite (hypSU h 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have heq : CFSG.Open.pRank 3 (⊤ : Subgroup (hypSU h 2 0)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup U) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e
  have hbound : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (hypSU h 2 0)) := by
    rcases Nat.even_or_odd n with hn' | hn'
    · exact hypSU_two_le_pRank_of_dvd_sub h (by norm_num : (3 : ℕ) ≠ 2)
        (n924x_three_dvd_two_pow_sub_one hn')
    · exact hypSU_two_le_pRank_of_dvd_add h (by norm_num : (3 : ℕ) ≠ 2)
        (n924x_three_dvd_two_pow_add_one hn')
  rw [heq] at hbound
  exact hbound

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
