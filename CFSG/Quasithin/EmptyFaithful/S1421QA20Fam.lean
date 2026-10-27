module

public import CFSG.Quasithin.EmptyFaithful.S1421QA20Num
public import CFSG.Quasithin.EmptyFaithful.T1515eC

public section

namespace CFSG.Quasithin.S1421QA20

open CFSG.Open

theorem l3Free_of_data {s z m c : ℕ} (hs : 3 ≤ s) (hz : 2 ^ s = z ^ 3) (hz16 : 16 ≤ z)
    (hm : Odd m) (hmc : m ≤ c * z ^ 4) (hc : 12 * c < z) : L3Free1515e (2 ^ s * m) 0 :=
  ⟨fun _ hq _ _ _ => not_eq_N_plus hs hz hz16 hm hmc hc hq (odd_gcd_three _) (gcd_three_le _),
    fun _ hq _ _ => not_eq_N_minus hs hz hz16 hm hmc hc hq (odd_gcd_three _) (gcd_three_le _)⟩

theorem pow_two_pow_eq (f k : ℕ) : (2 ^ f) ^ k = 2 ^ (k * f) := by
  rw [← pow_mul, mul_comm]

theorem l3Free_ordG2 {f : ℕ} (hf : 2 ≤ f) : L3Free1515e (ordG2 (2 ^ f)) 0 := by
  obtain ⟨y, hy⟩ : ∃ y, y = 2 ^ f := ⟨_, rfl⟩
  have hy4 : 4 ≤ y := by
    rw [hy]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hye : Even y := by rw [hy]; exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have h6 : 2 ^ (6 * f) = y ^ 6 := by rw [hy, pow_two_pow_eq]
  rw [← hy]
  have e : ordG2 y = 2 ^ (6 * f) * ((y ^ 6 - 1) * (y ^ 2 - 1)) := by
    unfold ordG2; rw [h6]; ring
  rw [e]
  refine l3Free_of_data (z := y ^ 2) (c := 1) (by omega) (by rw [h6]; ring) ?_ ?_ ?_ ?_
  · nlinarith
  · exact (odd_pow_sub_one hye (by omega) (by norm_num)).mul
      (odd_pow_sub_one hye (by omega) (by norm_num))
  · calc (y ^ 6 - 1) * (y ^ 2 - 1) ≤ y ^ 6 * y ^ 2 :=
          Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
      _ = 1 * (y ^ 2) ^ 4 := by ring
  · nlinarith

theorem l3Free_ordTrialityD4 {f : ℕ} (hf : 2 ≤ f) : L3Free1515e (ordTrialityD4 (2 ^ f)) 0 := by
  obtain ⟨y, hy⟩ : ∃ y, y = 2 ^ f := ⟨_, rfl⟩
  have hy4 : 4 ≤ y := by
    rw [hy]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hye : Even y := by rw [hy]; exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have h12 : 2 ^ (12 * f) = y ^ 12 := by rw [hy, pow_two_pow_eq]
  rw [← hy]
  have e : ordTrialityD4 y =
      2 ^ (12 * f) * ((y ^ 8 + y ^ 4 + 1) * ((y ^ 6 - 1) * (y ^ 2 - 1))) := by
    unfold ordTrialityD4; rw [h12]; ring
  rw [e]
  have hy44 : 256 ≤ y ^ 4 := by
    calc 256 = 4 ^ 4 := by norm_num
      _ ≤ y ^ 4 := Nat.pow_le_pow_left hy4 4
  refine l3Free_of_data (z := y ^ 4) (c := 2) (by omega) (by rw [h12]; ring) (by omega) ?_ ?_ ?_
  · have h1 : Odd (y ^ 8 + y ^ 4 + 1) := by
      have h8 : Even (y ^ 8) := Nat.even_pow.mpr ⟨hye, by norm_num⟩
      have h4 : Even (y ^ 4) := Nat.even_pow.mpr ⟨hye, by norm_num⟩
      exact (h8.add h4).add_one
    exact h1.mul ((odd_pow_sub_one hye (by omega) (by norm_num)).mul
      (odd_pow_sub_one hye (by omega) (by norm_num)))
  · have h1 : y ^ 8 + y ^ 4 + 1 ≤ 2 * y ^ 8 := by nlinarith
    calc (y ^ 8 + y ^ 4 + 1) * ((y ^ 6 - 1) * (y ^ 2 - 1))
        ≤ (2 * y ^ 8) * (y ^ 6 * y ^ 2) :=
          Nat.mul_le_mul h1 (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _))
      _ = 2 * (y ^ 4) ^ 4 := by ring
  · omega

theorem l3Free_ordTwistedF4 {f : ℕ} (hf : 3 ≤ f) : L3Free1515e (ordTwistedF4 (2 ^ f)) 0 := by
  obtain ⟨y, hy⟩ : ∃ y, y = 2 ^ f := ⟨_, rfl⟩
  have hy8 : 8 ≤ y := by
    rw [hy]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hye : Even y := by rw [hy]; exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have h12 : 2 ^ (12 * f) = y ^ 12 := by rw [hy, pow_two_pow_eq]
  rw [← hy]
  have e : ordTwistedF4 y = 2 ^ (12 * f) *
      ((y ^ 6 + 1) * ((y ^ 4 - 1) * ((y ^ 3 + 1) * (y - 1)))) := by
    unfold ordTwistedF4; rw [h12]; ring
  rw [e]
  have hy44 : 4096 ≤ y ^ 4 := by
    calc 4096 = 8 ^ 4 := by norm_num
      _ ≤ y ^ 4 := Nat.pow_le_pow_left hy8 4
  refine l3Free_of_data (z := y ^ 4) (c := 4) (by omega) (by rw [h12]; ring) (by omega) ?_ ?_ ?_
  · have hy1 : Odd (y - 1) := by
      have := odd_pow_sub_one hye (by omega) (one_ne_zero : 1 ≠ 0)
      simpa using this
    exact (odd_pow_add_one hye (by norm_num)).mul ((odd_pow_sub_one hye (by omega)
      (by norm_num)).mul ((odd_pow_add_one hye (by norm_num)).mul hy1))
  · have h6 : y ^ 6 + 1 ≤ 2 * y ^ 6 := by
      have : 1 ≤ y ^ 6 := Nat.one_le_pow _ _ (by omega)
      omega
    have h3 : y ^ 3 + 1 ≤ 2 * y ^ 3 := by
      have : 1 ≤ y ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega
    have h14 : y ^ 14 ≤ y ^ 16 := Nat.pow_le_pow_right (by omega) (by norm_num)
    calc (y ^ 6 + 1) * ((y ^ 4 - 1) * ((y ^ 3 + 1) * (y - 1)))
        ≤ (2 * y ^ 6) * (y ^ 4 * ((2 * y ^ 3) * y)) :=
          Nat.mul_le_mul h6 (Nat.mul_le_mul (Nat.sub_le _ _)
            (Nat.mul_le_mul h3 (Nat.sub_le _ _)))
      _ = 4 * y ^ 14 := by ring
      _ ≤ 4 * y ^ 16 := Nat.mul_le_mul_left _ h14
      _ = 4 * (y ^ 4) ^ 4 := by ring
  · omega

end CFSG.Quasithin.S1421QA20
