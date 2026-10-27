module

public import CFSG.Quasithin.Vol2.Ch11SecO7p

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE.C10KH

open CFSG.Open CFSG.Blueprint

theorem three_dvd_pow_even_sub_one (k j : ℕ) : 3 ∣ (2 ^ k) ^ (2 * j) - 1 := by
  have e : (2 ^ k) ^ (2 * j) = (2 ^ (k * j)) ^ 2 := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [e]
  exact three_dvd_sq_sub_one (k * j)

theorem profile_f4 {k N : ℕ} (hk : 1 ≤ k) (hN : N = ordTwistedF4 (2 ^ k)) :
    Profile N (12 * k)
      (((2 ^ k) ^ 6 + 1) * ((2 ^ k) ^ 4 - 1) * ((2 ^ k) ^ 3 + 1) * (2 ^ k - 1)) := by
  have hs : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h3 : 3 ∣ (2 ^ k) ^ 4 - 1 := by
    have := three_dvd_pow_even_sub_one k 2
    simpa using this
  have hodd : Odd (((2 ^ k) ^ 6 + 1) * ((2 ^ k) ^ 4 - 1) * ((2 ^ k) ^ 3 + 1) * (2 ^ k - 1)) := by
    have h6 : Odd ((2 ^ k) ^ 6 + 1) :=
      (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩).add_one
    have h3' : Odd ((2 ^ k) ^ 3 + 1) :=
      (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩).add_one
    have h1 : Odd (2 ^ k - 1) := by simpa using odd_pow k 1 hk le_rfl
    exact ((h6.mul (odd_pow k 4 hk (by norm_num))).mul h3').mul h1
  have e12 : 2 ^ (12 * k) = (2 ^ k) ^ 12 := by rw [← pow_mul, mul_comm]
  refine ⟨by rw [hN, ordTwistedF4, e12]; ring, hodd,
    Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left h3 _) _) _, ?_, ?_⟩
  · generalize 2 ^ k = s at hs ⊢
    have e1 : 65 ≤ s ^ 6 + 1 := by have := Nat.pow_le_pow_left hs 6; omega
    have e2 : 15 ≤ s ^ 4 - 1 :=
      le_pow_sub_one ((by norm_num : 15 + 1 ≤ 2 ^ 4).trans (Nat.pow_le_pow_left hs 4))
    have e3 : 9 ≤ s ^ 3 + 1 := by have := Nat.pow_le_pow_left hs 3; omega
    have e4 : 1 ≤ s - 1 := by omega
    exact (by norm_num : 315 ≤ 65 * 15 * 9 * 1).trans
      (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul e1 e2) e3) e4)
  · rw [e12]
    generalize 2 ^ k = s at hs ⊢
    have e1 : s ^ 6 + 1 ≤ 2 * s ^ 6 := by have := Nat.one_le_pow 6 s (by omega); omega
    have e3 : s ^ 3 + 1 ≤ 2 * s ^ 3 := by have := Nat.one_le_pow 3 s (by omega); omega
    have hu : (s ^ 6 + 1) * (s ^ 4 - 1) * (s ^ 3 + 1) * (s - 1) ≤
        2 * s ^ 6 * s ^ 4 * (2 * s ^ 3) * s :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul e1 (Nat.sub_le _ _)) e3) (Nat.sub_le _ _)
    have e : 2 * s ^ 6 * s ^ 4 * (2 * s ^ 3) * s = 4 * s ^ 14 := by ring
    have h10 : 16 < s ^ 10 := (by norm_num : 16 < 2 ^ 10).trans_le (Nat.pow_le_pow_left hs 10)
    have e' : (s ^ 12) ^ 2 = s ^ 10 * s ^ 14 := by ring
    rw [e']
    have hp : 0 < s ^ 14 := by positivity
    calc 4 * ((s ^ 6 + 1) * (s ^ 4 - 1) * (s ^ 3 + 1) * (s - 1)) ≤ 4 * (4 * s ^ 14) :=
          Nat.mul_le_mul_left _ (e ▸ hu)
      _ = 16 * s ^ 14 := by ring
      _ < s ^ 10 * s ^ 14 := Nat.mul_lt_mul_of_pos_right h10 hp

theorem profile_d4 {k N : ℕ} (hk : 1 ≤ k) (hN : N = ordTrialityD4 (2 ^ k)) :
    Profile N (12 * k)
      (((2 ^ k) ^ 8 + (2 ^ k) ^ 4 + 1) * ((2 ^ k) ^ 6 - 1) * ((2 ^ k) ^ 2 - 1)) := by
  have hs : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hodd : Odd (((2 ^ k) ^ 8 + (2 ^ k) ^ 4 + 1) * ((2 ^ k) ^ 6 - 1) * ((2 ^ k) ^ 2 - 1)) := by
    refine Odd.mul (Odd.mul ?_ (odd_pow k 6 hk (by norm_num))) (odd_pow k 2 hk (by norm_num))
    have h1 : Even ((2 ^ k) ^ 8 + (2 ^ k) ^ 4) := by
      rw [← pow_mul, ← pow_mul]
      exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).add (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    exact h1.add_one
  have e12 : 2 ^ (12 * k) = (2 ^ k) ^ 12 := by rw [← pow_mul, mul_comm]
  refine ⟨by rw [hN, ordTrialityD4, e12]; ring, hodd,
    Dvd.dvd.mul_left (three_dvd_sq_sub_one k) _, ?_, ?_⟩
  · generalize 2 ^ k = s at hs ⊢
    have e1 : 273 ≤ s ^ 8 + s ^ 4 + 1 := by
      have := Nat.pow_le_pow_left hs 8
      have := Nat.pow_le_pow_left hs 4
      omega
    have e2 : 63 ≤ s ^ 6 - 1 :=
      le_pow_sub_one ((by norm_num : 63 + 1 ≤ 2 ^ 6).trans (Nat.pow_le_pow_left hs 6))
    have e3 : 3 ≤ s ^ 2 - 1 :=
      le_pow_sub_one ((by norm_num : 3 + 1 ≤ 2 ^ 2).trans (Nat.pow_le_pow_left hs 2))
    exact (by norm_num : 315 ≤ 273 * 63 * 3).trans (Nat.mul_le_mul (Nat.mul_le_mul e1 e2) e3)
  · rw [e12]
    generalize 2 ^ k = s at hs ⊢
    have e1 : s ^ 8 + s ^ 4 + 1 ≤ 3 * s ^ 8 := by
      have h4 : s ^ 4 ≤ s ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
      have := Nat.one_le_pow 4 s (by omega)
      omega
    have hu : (s ^ 8 + s ^ 4 + 1) * (s ^ 6 - 1) * (s ^ 2 - 1) ≤ 3 * s ^ 8 * s ^ 6 * s ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul e1 (Nat.sub_le _ _)) (Nat.sub_le _ _)
    have e : 3 * s ^ 8 * s ^ 6 * s ^ 2 = 3 * s ^ 16 := by ring
    have h8 : 12 < s ^ 8 := (by norm_num : 12 < 2 ^ 8).trans_le (Nat.pow_le_pow_left hs 8)
    have e' : (s ^ 12) ^ 2 = s ^ 8 * s ^ 16 := by ring
    rw [e']
    have hp : 0 < s ^ 16 := by positivity
    calc 4 * ((s ^ 8 + s ^ 4 + 1) * (s ^ 6 - 1) * (s ^ 2 - 1)) ≤ 4 * (3 * s ^ 16) :=
          Nat.mul_le_mul_left _ (e ▸ hu)
      _ = 12 * s ^ 16 := by ring
      _ < s ^ 8 * s ^ 16 := Nat.mul_lt_mul_of_pos_right h8 hp

end CFSG.Quasithin.Vol2.Ch11.SecE.C10KH
