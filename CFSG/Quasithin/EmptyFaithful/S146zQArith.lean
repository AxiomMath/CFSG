module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Factors

public section

namespace CFSG.Quasithin

theorem four_pow_mod_five (k : ℕ) : 4 ^ k % 5 = 1 ∨ 4 ^ k % 5 = 4 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> simp [h]

theorem prime_dvd_two_pow_sub_one_ge_seven {m r : ℕ} (hm : Odd m) (hm1 : 1 < m) (hr : r.Prime)
    (hd : r ∣ 2 ^ m - 1) : 7 ≤ r := by
  by_contra hlt
  push Not at hlt
  obtain ⟨k, rfl⟩ := hm
  have hx : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    norm_num
    omega
  have h3 : 4 ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h5 := four_pow_mod_five k
  have hpos : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  rw [hx] at hd
  interval_cases r
  · exact absurd hr (by norm_num)
  · exact absurd hr (by norm_num)
  · omega
  · omega
  · exact absurd hr (by norm_num)
  · omega
  · exact absurd hr (by norm_num)

theorem three_pow_mod_eight (a : ℕ) : 3 ^ a % 8 = 1 ∨ 3 ^ a % 8 = 3 := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> simp [h]

theorem two_pow_sub_one_eq_three_pow {m a : ℕ} (hm : 2 ≤ m) (h : 2 ^ m - 1 = 3 ^ a) : m = 2 := by
  by_contra hne
  have hm3 : 3 ≤ m := by omega
  have h8 : 2 ^ m % 8 = 0 := by
    have h8dvd : (8 : ℕ) ∣ 2 ^ m :=
      ⟨2 ^ (m - 3), by rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega⟩
    exact Nat.mod_eq_zero_of_dvd h8dvd
  have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h3 := three_pow_mod_eight a
  omega

theorem m_eq_two_of_prime_dvd {m : ℕ} (hm : 2 ≤ m)
    (h : ∀ r : ℕ, r.Prime → r ∣ 2 ^ m - 1 → r = 3) : m = 2 := by
  have hne : 2 ^ m - 1 ≠ 0 := by
    have : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact two_pow_sub_one_eq_three_pow hm
    (Nat.eq_prime_pow_of_unique_prime_dvd hne (fun {d} hd hdv => h d hd hdv))

theorem four_dvd_of_five_dvd_two_pow_sub_one {m : ℕ} (h : 5 ∣ 2 ^ m - 1) : 4 ∣ m := by
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < 4 ∧ m = 4 * q + s :=
    ⟨m / 4, m % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 4).symm⟩
  have h16 : (2 : ℕ) ^ (4 * q) % 5 = 1 := by
    rw [pow_mul, Nat.pow_mod]
    norm_num
  have hx : (2 : ℕ) ^ (4 * q + s) = 2 ^ (4 * q) * 2 ^ s := pow_add _ _ _
  have hB : 2 ^ s = 1 ∨ 2 ^ s = 2 ∨ 2 ^ s = 4 ∨ 2 ^ s = 8 := by
    interval_cases s <;> simp
  have hpos : 1 ≤ (2 : ℕ) ^ (4 * q) := Nat.one_le_two_pow
  rw [hx] at h
  rcases hB with hB | hB | hB | hB
  · have : s = 0 := by
      by_contra hne
      have : 2 ≤ 2 ^ s := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  · rw [hB] at h; omega
  · rw [hB] at h; omega
  · rw [hB] at h; omega

theorem m_eq_four_of_prime_dvd {m : ℕ} (hm : 2 ≤ m) (h5 : 5 ∣ 2 ^ m - 1)
    (h : ∀ r : ℕ, r.Prime → r ∣ 2 ^ m - 1 → r = 3 ∨ r = 5) : m = 4 := by
  obtain ⟨k, rfl⟩ := four_dvd_of_five_dvd_two_pow_sub_one h5
  have hk : 1 ≤ k := by omega
  by_contra hne
  have hk2 : 2 ≤ k := by omega
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | hodd
  ·
    have h1 := Nat.sub_dvd_pow_sub_pow (2 ^ 8) 1 j
    have hm8 : (2 : ℕ) ^ (4 * k) = (2 ^ 8) ^ j := by
      rw [← pow_mul]; congr 1; omega
    have h17 : 17 ∣ 2 ^ (4 * k) - 1 := by
      rw [hm8]
      have : (17 : ℕ) ∣ 2 ^ 8 - 1 := by norm_num
      simpa using this.trans h1
    rcases h 17 (by norm_num) h17 with e | e <;> omega
  ·
    have hk3 : 2 ≤ 2 ^ k - 1 := by
      have : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      omega
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (show 2 ^ k - 1 ≠ 1 by omega)
    have h1 := Nat.sub_dvd_pow_sub_pow (2 ^ k) 1 4
    have hmk : (2 : ℕ) ^ (4 * k) = (2 ^ k) ^ 4 := by
      rw [← pow_mul]; congr 1; omega
    have hrm : r ∣ 2 ^ (4 * k) - 1 := by
      rw [hmk]
      simpa using hrd.trans h1
    have h7 := prime_dvd_two_pow_sub_one_ge_seven hodd (by omega) hr hrd
    rcases h r hr hrm with e | e <;> omega

end CFSG.Quasithin
