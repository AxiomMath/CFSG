module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

private lemma k330c_le_two_mul_pred (m : ℕ) (hm : 2 ≤ m) : m ≤ 2 * (m - 1) := by
  omega

private lemma k330c_three_mul_pred_le (m : ℕ) (hm : 4 ≤ m) : 3 * m ≤ 4 * (m - 1) := by
  omega

theorem sltBound_lt_torusLow (n : ℕ) (hn : n = 4 ∨ n = 5) (k : ℕ) (hk : 2 ≤ k) :
    sltBound n k < torusLow n (k ^ 7) := by
  rcases hn with rfl | rfl
  · rw [show sltBound 4 k = k ^ 15 by norm_num [sltBound],
      show torusLow 4 (k ^ 7) = (k ^ 7 - 1) ^ 3 / 4 by norm_num [torusLow]]
    have hm : 128 ≤ k ^ 7 := by
      calc 128 = 2 ^ 7 := by norm_num
        _ ≤ k ^ 7 := Nat.pow_le_pow_left hk 7
    have hle : k ^ 7 ≤ 2 * (k ^ 7 - 1) := k330c_le_two_mul_pred (k ^ 7) (by omega)
    have h1 : (k ^ 7) ^ 3 ≤ 8 * (k ^ 7 - 1) ^ 3 := by
      have h := Nat.pow_le_pow_left hle 3
      rw [Nat.mul_pow] at h
      norm_num at h
      exact h
    have h2 : (k ^ 7) ^ 3 = k ^ 21 := by
      rw [← Nat.pow_mul]
    have h3 : 64 ≤ k ^ 6 := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ k ^ 6 := Nat.pow_le_pow_left hk 6
    have h4 : 64 * k ^ 15 ≤ k ^ 21 := by
      have e : k ^ 21 = k ^ 6 * k ^ 15 := by
        rw [← Nat.pow_add]
      rw [e]
      exact Nat.mul_le_mul_right _ h3
    have h5 : 8 * k ^ 15 ≤ (k ^ 7 - 1) ^ 3 := by
      rw [h2] at h1
      have h : 64 * k ^ 15 ≤ 8 * (k ^ 7 - 1) ^ 3 := le_trans h4 h1
      have h' : 8 * (8 * k ^ 15) ≤ 8 * (k ^ 7 - 1) ^ 3 := by
        calc 8 * (8 * k ^ 15) = 64 * k ^ 15 := by ring
          _ ≤ 8 * (k ^ 7 - 1) ^ 3 := h
      exact Nat.le_of_mul_le_mul_left h' (by norm_num)
    have hk15 : 1 ≤ k ^ 15 := Nat.one_le_pow 15 k (by omega)
    have h8 : 4 * k ^ 15 + 3 < 8 * k ^ 15 := by omega
    have h7 : 4 * k ^ 15 + 3 < (k ^ 7 - 1) ^ 3 := lt_of_lt_of_le h8 h5
    have h9 : 4 * k ^ 15 < (k ^ 7 - 1) ^ 3 - 3 := Nat.lt_sub_iff_add_lt.mpr h7
    have h10 : k ^ 15 * 4 < (k ^ 7 - 1) ^ 3 - 3 := by
      rw [mul_comm]
      exact h9
    have h11 := (Nat.lt_div_iff_mul_lt (show 0 < (4 : ℕ) by norm_num)).mpr h10
    simpa using h11
  · rw [show sltBound 5 k = k ^ 24 by norm_num [sltBound],
      show torusLow 5 (k ^ 7) = (((k ^ 7) ^ 2 - 1) ^ 2) / 5 by norm_num [torusLow]]
    rw [show (k ^ 7) ^ 2 = k ^ 14 by rw [← Nat.pow_mul]]
    have hm2 : 4 ≤ k ^ 14 := by
      have hk2 : 4 ≤ k ^ 2 := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ k ^ 2 := Nat.pow_le_pow_left hk 2
      exact le_trans hk2 (Nat.pow_le_pow_right (by omega) (by norm_num : 2 ≤ 14))
    have hs : 3 * k ^ 14 ≤ 4 * (k ^ 14 - 1) := k330c_three_mul_pred_le (k ^ 14) hm2
    have h1 : 9 * (k ^ 14) ^ 2 ≤ 16 * (k ^ 14 - 1) ^ 2 := by
      have h := Nat.pow_le_pow_left hs 2
      have e1 : (3 * k ^ 14) ^ 2 = 9 * (k ^ 14) ^ 2 := by ring
      have e2 : (4 * (k ^ 14 - 1)) ^ 2 = 16 * (k ^ 14 - 1) ^ 2 := by ring
      rw [e1, e2] at h
      exact h
    have h2 : (k ^ 14) ^ 2 = k ^ 28 := by
      rw [← Nat.pow_mul]
    have h1' : 9 * k ^ 28 ≤ 16 * (k ^ 14 - 1) ^ 2 := by
      rw [h2] at h1
      exact h1
    have h3 : 16 ≤ k ^ 4 := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ k ^ 4 := Nat.pow_le_pow_left hk 4
    have h4 : 144 * k ^ 24 ≤ 9 * k ^ 28 := by
      have e : k ^ 28 = k ^ 4 * k ^ 24 := by
        rw [← Nat.pow_add]
      rw [e]
      calc 144 * k ^ 24 = 9 * (16 * k ^ 24) := by ring
        _ ≤ 9 * (k ^ 4 * k ^ 24) := Nat.mul_le_mul_left 9 (Nat.mul_le_mul_right _ h3)
    have h5 : 144 * k ^ 24 ≤ 16 * (k ^ 14 - 1) ^ 2 := le_trans h4 h1'
    have h6 : 9 * k ^ 24 ≤ (k ^ 14 - 1) ^ 2 := by
      have h' : 16 * (9 * k ^ 24) ≤ 16 * (k ^ 14 - 1) ^ 2 := by
        calc 16 * (9 * k ^ 24) = 144 * k ^ 24 := by ring
          _ ≤ 16 * (k ^ 14 - 1) ^ 2 := h5
      exact Nat.le_of_mul_le_mul_left h' (by norm_num)
    have hk24 : 2 ≤ k ^ 24 := by
      have hk1 : 1 < k := by omega
      have h := Nat.one_lt_pow (by norm_num : 24 ≠ 0) hk1
      omega
    have h8 : 5 * k ^ 24 + 4 < 9 * k ^ 24 := by omega
    have h7 : 5 * k ^ 24 + 4 < (k ^ 14 - 1) ^ 2 := lt_of_lt_of_le h8 h6
    have h9 : 5 * k ^ 24 < (k ^ 14 - 1) ^ 2 - 4 := Nat.lt_sub_iff_add_lt.mpr h7
    have h10 : k ^ 24 * 5 < (k ^ 14 - 1) ^ 2 - 4 := by
      rw [mul_comm]
      exact h9
    have h11 := (Nat.lt_div_iff_mul_lt (show 0 < (5 : ℕ) by norm_num)).mpr h10
    simpa using h11

theorem spBound_lt_spTorusLow (k : ℕ) (hk : 2 ≤ k) : spBound k < spTorusLow (k ^ 7) := by
  have hm2 : 2 ≤ k ^ 7 := by
    calc 2 ≤ 2 ^ 7 := by norm_num
      _ ≤ k ^ 7 := Nat.pow_le_pow_left hk 7
  have hle : k ^ 7 ≤ 2 * (k ^ 7 - 1) := k330c_le_two_mul_pred (k ^ 7) hm2
  have h1 : (k ^ 7) ^ 2 ≤ 4 * (k ^ 7 - 1) ^ 2 := by
    have h := Nat.pow_le_pow_left hle 2
    rw [Nat.mul_pow] at h
    norm_num at h
    exact h
  have h2 : (k ^ 7) ^ 2 = k ^ 14 := by
    rw [← Nat.pow_mul]
  have h1' : k ^ 14 ≤ 4 * (k ^ 7 - 1) ^ 2 := by
    rw [h2] at h1
    exact h1
  have h3 : 16 ≤ k ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ k ^ 4 := Nat.pow_le_pow_left hk 4
  have h4 : 16 * k ^ 10 ≤ k ^ 14 := by
    have e : k ^ 14 = k ^ 4 * k ^ 10 := by
      rw [← Nat.pow_add]
    rw [e]
    exact Nat.mul_le_mul_right _ h3
  have h5 : 16 * k ^ 10 ≤ 4 * (k ^ 7 - 1) ^ 2 := le_trans h4 h1'
  have h6 : 4 * k ^ 10 ≤ (k ^ 7 - 1) ^ 2 := by
    have h' : 4 * (4 * k ^ 10) ≤ 4 * (k ^ 7 - 1) ^ 2 := by
      calc 4 * (4 * k ^ 10) = 16 * k ^ 10 := by ring
        _ ≤ 4 * (k ^ 7 - 1) ^ 2 := h5
    exact Nat.le_of_mul_le_mul_left h' (by norm_num)
  have hk10 : 1 ≤ k ^ 10 := Nat.one_le_pow 10 k (by omega)
  have h7 : 2 * k ^ 10 + 1 < 4 * k ^ 10 := by omega
  have h8 : 2 * k ^ 10 + 1 < (k ^ 7 - 1) ^ 2 := lt_of_lt_of_le h7 h6
  have h9 : 2 * k ^ 10 < (k ^ 7 - 1) ^ 2 - 1 := Nat.lt_sub_iff_add_lt.mpr h8
  have h10 : k ^ 10 * 2 < (k ^ 7 - 1) ^ 2 - 1 := by
    rw [mul_comm]
    exact h9
  have h11 := (Nat.lt_div_iff_mul_lt (show 0 < (2 : ℕ) by norm_num)).mpr h10
  simpa [spBound, spTorusLow] using h11

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
