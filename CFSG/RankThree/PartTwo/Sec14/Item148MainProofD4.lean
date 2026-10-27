module

import CFSG.RankThree.PartTwo.Sec14.Item148StepFieldTypes
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Main148

theorem card_ne_of_isoLThreePi_two148 {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : Sec4.IsoLThreePi X 2 n) {N : ℕ}
    (hN : N = 604800 ∨ N = 443520 ∨ N = 95040 ∨ N = 2520) : Nat.card X ≠ N := by
  intro hX
  have hg1 : Nat.gcd 3 (2 ^ n - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hg2 : Nat.gcd 3 (2 ^ n + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hQ : 2 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  have hM1 : 1 ≤ ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) := by
    have : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
    have : 8 ≤ (2 ^ n) ^ 3 := by nlinarith
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hM2 : 1 ≤ ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) := by
    have : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hn7 : n ≤ 7 := by
    by_contra hlt
    push Not at hlt
    have hQ8 : 256 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hlt)
    have hQ3 : 256 ^ 3 ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hQ8 3
    rcases card_mul_gcd_of_isoLThreePi_two hn h with he | he <;> rw [hX] at he <;>
      rcases hN with rfl | rfl | rfl | rfl <;> nlinarith
  interval_cases n <;> rcases card_mul_gcd_of_isoLThreePi_two hn h with he | he <;>
    rw [hX] at he <;> rcases hN with rfl | rfl | rfl | rfl <;> norm_num at he

end Main148

open Main148

end CFSG.RankThree.PartTwo.Sec14
