module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch11SecO7g

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE.C10KH

open CFSG.Open CFSG.Blueprint

@[expose] def Profile (N A u : ℕ) : Prop :=
  N = 2 ^ A * u ∧ Odd u ∧ 3 ∣ u ∧ 315 ≤ u ∧ 4 * u < (2 ^ A) ^ 2

theorem three_dvd_sq_sub_one (n : ℕ) : 3 ∣ (2 ^ n) ^ 2 - 1 := by
  have h := Nat.sub_one_dvd_pow_sub_one 4 n
  rw [← pow_mul, mul_comm, pow_mul]
  exact h

theorem four_le_two_pow {n : ℕ} (hn : 2 ≤ n) : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := rfl
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem four_mul_lt {s a b c : ℕ} (hs : 2 ≤ s)
    (h : 4 * (s ^ a * s ^ b) ≤ (s ^ c) ^ 2) : 4 * ((s ^ a - 1) * (s ^ b - 1)) < (s ^ c) ^ 2 := by
  have h1 : 1 ≤ s ^ a := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ s ^ b := Nat.one_le_pow _ _ (by omega)
  have h3 : (s ^ a - 1) * (s ^ b - 1) < s ^ a * s ^ b :=
    Nat.mul_lt_mul_of_lt_of_le (by omega) (Nat.sub_le _ _) (by omega)
  omega

theorem le_pow_sub_one {s k m : ℕ} (h : m + 1 ≤ s ^ k) : m ≤ s ^ k - 1 := by omega

theorem profile_sl3 {n N : ℕ} (hn : 2 ≤ n)
    (hN : N = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1))) :
    Profile N (3 * n) (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
  have hs := four_le_two_pow hn
  have ea : 2 ^ (3 * n) = (2 ^ n) ^ 3 := by rw [← pow_mul, mul_comm]
  refine ⟨by rw [hN, ea], (odd_pow n 2 (by omega) (by norm_num)).mul
    (odd_pow n 3 (by omega) (by norm_num)), Dvd.dvd.mul_right (three_dvd_sq_sub_one n) _, ?_, ?_⟩
  · generalize 2 ^ n = s at hs ⊢
    have h2 : 15 ≤ s ^ 2 - 1 :=
      le_pow_sub_one ((by norm_num : 15 + 1 ≤ 4 ^ 2).trans (Nat.pow_le_pow_left hs 2))
    have h3 : 63 ≤ s ^ 3 - 1 :=
      le_pow_sub_one ((by norm_num : 63 + 1 ≤ 4 ^ 3).trans (Nat.pow_le_pow_left hs 3))
    exact (by norm_num : 315 ≤ 15 * 63).trans (Nat.mul_le_mul h2 h3)
  · rw [ea]
    generalize 2 ^ n = s at hs ⊢
    refine four_mul_lt (by omega) ?_
    have : (s ^ 3) ^ 2 = s * (s ^ 2 * s ^ 3) := by ring
    rw [this]
    exact Nat.mul_le_mul_right _ hs

theorem profile_sp4 {n N : ℕ} (hn : 2 ≤ n)
    (hN : N = (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1))) :
    Profile N (4 * n) (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) := by
  have hs := four_le_two_pow hn
  have ea : 2 ^ (4 * n) = (2 ^ n) ^ 4 := by rw [← pow_mul, mul_comm]
  refine ⟨by rw [hN, ea], (odd_pow n 2 (by omega) (by norm_num)).mul
    (odd_pow n 4 (by omega) (by norm_num)), Dvd.dvd.mul_right (three_dvd_sq_sub_one n) _, ?_, ?_⟩
  · generalize 2 ^ n = s at hs ⊢
    have h2 : 15 ≤ s ^ 2 - 1 :=
      le_pow_sub_one ((by norm_num : 15 + 1 ≤ 4 ^ 2).trans (Nat.pow_le_pow_left hs 2))
    have h4 : 255 ≤ s ^ 4 - 1 :=
      le_pow_sub_one ((by norm_num : 255 + 1 ≤ 4 ^ 4).trans (Nat.pow_le_pow_left hs 4))
    exact (by norm_num : 315 ≤ 15 * 255).trans (Nat.mul_le_mul h2 h4)
  · rw [ea]
    generalize 2 ^ n = s at hs ⊢
    refine four_mul_lt (by omega) ?_
    have : (s ^ 4) ^ 2 = s ^ 2 * (s ^ 2 * s ^ 4) := by ring
    rw [this]
    exact Nat.mul_le_mul_right _ ((by norm_num : 4 ≤ 4 ^ 2).trans (Nat.pow_le_pow_left hs 2))

theorem profile_g2 {n N : ℕ} (hn : 2 ≤ n)
    (hN : N = (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1))) :
    Profile N (6 * n) (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) := by
  have hs := four_le_two_pow hn
  have ea : 2 ^ (6 * n) = (2 ^ n) ^ 6 := by rw [← pow_mul, mul_comm]
  refine ⟨by rw [hN, ea], (odd_pow n 6 (by omega) (by norm_num)).mul
    (odd_pow n 2 (by omega) (by norm_num)), Dvd.dvd.mul_left (three_dvd_sq_sub_one n) _, ?_, ?_⟩
  · generalize 2 ^ n = s at hs ⊢
    have h2 : 15 ≤ s ^ 2 - 1 :=
      le_pow_sub_one ((by norm_num : 15 + 1 ≤ 4 ^ 2).trans (Nat.pow_le_pow_left hs 2))
    have h6 : 4095 ≤ s ^ 6 - 1 :=
      le_pow_sub_one ((by norm_num : 4095 + 1 ≤ 4 ^ 6).trans (Nat.pow_le_pow_left hs 6))
    exact (by norm_num : 315 ≤ 4095 * 15).trans (Nat.mul_le_mul h6 h2)
  · rw [ea]
    generalize 2 ^ n = s at hs ⊢
    refine four_mul_lt (by omega) ?_
    have : (s ^ 6) ^ 2 = s ^ 4 * (s ^ 6 * s ^ 2) := by ring
    rw [this]
    exact Nat.mul_le_mul_right _ ((by norm_num : 4 ≤ 4 ^ 4).trans (Nat.pow_le_pow_left hs 4))

end CFSG.Quasithin.Vol2.Ch11.SecE.C10KH
