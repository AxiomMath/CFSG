module

public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.PartTwo.KFacts.OddChar

open Finset

variable {q : ℕ}

theorem two_pow_padicValNat_le {n : ℕ} (hn : n ≠ 0) : 2 ^ padicValNat 2 n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd

theorem padicValNat_odd_pow_mul (hq : Odd q) (a : ℕ) {x : ℕ} (hx : x ≠ 0) :
    padicValNat 2 (q ^ a * x) = padicValNat 2 x := by
  rw [padicValNat.mul (pow_ne_zero _ hq.pos.ne') hx, padicValNat.pow,
    padicValNat.eq_zero_of_not_dvd hq.not_two_dvd_nat, mul_zero, zero_add]

theorem padicValNat_eq_one_of_mod_four {n : ℕ} (hn : n % 4 = 2) : padicValNat 2 n = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * (2 * k + 1) := ⟨n / 4, by omega⟩
  rw [padicValNat.mul two_ne_zero (by omega), padicValNat.self one_lt_two,
    padicValNat.eq_zero_of_not_dvd (by omega)]

theorem padicValNat_sub_one_eq_one_or (hq : Odd q) :
    padicValNat 2 (q - 1) = 1 ∨ padicValNat 2 (q + 1) = 1 := by
  have h := Nat.odd_iff.mp hq
  rcases (show q % 4 = 1 ∨ q % 4 = 3 by omega) with h4 | h4
  · exact Or.inr (padicValNat_eq_one_of_mod_four (by omega))
  · exact Or.inl (padicValNat_eq_one_of_mod_four (by omega))

theorem padicValNat_sq_sub_one (hq : Odd q) (hq1 : 1 < q) :
    padicValNat 2 (q ^ 2 - 1) = padicValNat 2 (q - 1) + padicValNat 2 (q + 1) := by
  have h := padicValNat.pow_two_sub_one hq1 hq.not_two_dvd_nat two_ne_zero even_two
  rw [padicValNat.self one_lt_two] at h
  omega

theorem padicValNat_pow_two_mul_sub_one (hq : Odd q) (hq1 : 1 < q) {k : ℕ} (hk : k ≠ 0) :
    padicValNat 2 (q ^ (2 * k) - 1) = padicValNat 2 (q ^ 2 - 1) + padicValNat 2 k := by
  have h := padicValNat.pow_two_sub_one hq1 hq.not_two_dvd_nat (n := 2 * k) (by omega)
    (even_two_mul k)
  rw [padicValNat.mul two_ne_zero hk, padicValNat.self one_lt_two] at h
  rw [padicValNat_sq_sub_one hq hq1]
  omega

theorem padicValNat_pow_three_sub_one (hq : Odd q) (hq1 : 1 < q) :
    padicValNat 2 (q ^ 3 - 1) = padicValNat 2 (q - 1) := by
  obtain ⟨s, rfl⟩ := hq
  have he : (2 * s + 1) ^ 3 - 1 = (2 * s + 1 - 1) * (2 * (2 * s ^ 2 + 3 * s + 1) + 1) := by
    rw [Nat.add_sub_cancel]
    have : (2 * s + 1) ^ 3 = 2 * s * (2 * (2 * s ^ 2 + 3 * s + 1) + 1) + 1 := by ring
    omega
  have h1 : 2 * s + 1 - 1 ≠ 0 := by omega
  have h2 : ¬ 2 ∣ 2 * (2 * s ^ 2 + 3 * s + 1) + 1 := by omega
  rw [he, padicValNat.mul h1 (by omega), padicValNat.eq_zero_of_not_dvd h2, add_zero]

theorem padicValNat_pow_three_add_one (hq : Odd q) :
    padicValNat 2 (q ^ 3 + 1) = padicValNat 2 (q + 1) := by
  obtain ⟨s, rfl⟩ := hq
  have he : (2 * s + 1) ^ 3 + 1 = (2 * s + 1 + 1) * (2 * (s * (2 * s + 1)) + 1) := by ring
  have h2 : ¬ 2 ∣ 2 * (s * (2 * s + 1)) + 1 := by omega
  rw [he, padicValNat.mul (by omega) (by omega), padicValNat.eq_zero_of_not_dvd h2, add_zero]

theorem padicValNat_pow_sub_one_le_of_odd (hq : Odd q) (hq1 : 1 < q) {j : ℕ} (hj : Odd j) :
    padicValNat 2 (q ^ j - 1) ≤ padicValNat 2 (q ^ 2 - 1) := by
  have hj0 : j ≠ 0 := hj.pos.ne'
  have h2j : q ^ (2 * j) - 1 ≠ 0 := by
    have : 1 < q ^ (2 * j) := Nat.one_lt_pow (by omega) hq1
    omega
  have hdvd : q ^ j - 1 ∣ q ^ (2 * j) - 1 := by
    rw [mul_comm, pow_mul]
    exact Nat.sub_one_dvd_pow_sub_one _ _
  have hle : padicValNat 2 (q ^ j - 1) ≤ padicValNat 2 (q ^ (2 * j) - 1) :=
    (padicValNat_dvd_iff_le h2j).mp (pow_padicValNat_dvd.trans hdvd)
  rwa [padicValNat_pow_two_mul_sub_one hq hq1 hj0,
    padicValNat.eq_zero_of_not_dvd hj.not_two_dvd_nat, add_zero] at hle

theorem two_pow_padicValNat_sq_sub_one_le (hq : Odd q) (hq1 : 1 < q) :
    2 ^ padicValNat 2 (q ^ 2 - 1) ≤ 2 * (q + 1) := by
  rw [padicValNat_sq_sub_one hq hq1, pow_add]
  rcases padicValNat_sub_one_eq_one_or hq with h | h
  · rw [h, pow_one]
    exact Nat.mul_le_mul_left 2 (two_pow_padicValNat_le (by omega))
  · rw [h, pow_one, mul_comm]
    have := two_pow_padicValNat_le (n := q - 1) (by omega)
    omega

theorem two_pow_padicValNat_sl_three_le (hq : Odd q) (hq3 : 3 ≤ q) :
    2 ^ (padicValNat 2 (q ^ 2 - 1) + padicValNat 2 (q ^ 3 - 1)) ≤ 2 * (q ^ 2 - 1) := by
  have hq1 : 1 < q := by omega
  have hsq : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    have : (t + 1) ^ 2 = (t + 1 + 1) * t + 1 := by ring
    rw [Nat.add_sub_cancel]
    omega
  rw [padicValNat_sq_sub_one hq hq1, padicValNat_pow_three_sub_one hq hq1, hsq]
  have hm := two_pow_padicValNat_le (n := q - 1) (by omega)
  have hp := two_pow_padicValNat_le (n := q + 1) (by omega)
  rcases padicValNat_sub_one_eq_one_or hq with h | h
  · rw [h, show 1 + padicValNat 2 (q + 1) + 1 = padicValNat 2 (q + 1) + 2 by omega, pow_add]
    calc 2 ^ padicValNat 2 (q + 1) * 2 ^ 2 ≤ (q + 1) * 4 := Nat.mul_le_mul_right _ hp
      _ ≤ 2 * ((q + 1) * (q - 1)) := by
        rw [mul_comm 2, mul_assoc]
        exact Nat.mul_le_mul_left _ (by omega)
  · rw [h, show padicValNat 2 (q - 1) + 1 + padicValNat 2 (q - 1) =
      1 + (padicValNat 2 (q - 1) + padicValNat 2 (q - 1)) by omega, pow_add, pow_add, pow_one]
    calc 2 * (2 ^ padicValNat 2 (q - 1) * 2 ^ padicValNat 2 (q - 1))
        ≤ 2 * ((q - 1) * (q - 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hm hm)
      _ ≤ 2 * ((q + 1) * (q - 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))

theorem two_pow_padicValNat_pow_sub_one_le (hq : Odd q) (hq1 : 1 < q) {j : ℕ} (hj : 2 ≤ j) :
    2 ^ padicValNat 2 (q ^ j - 1) ≤ (q + 1) * j := by
  have h2 := two_pow_padicValNat_sq_sub_one_le hq hq1
  rcases Nat.even_or_odd j with ⟨k, rfl⟩ | hjo
  · rw [← two_mul, padicValNat_pow_two_mul_sub_one hq hq1 (by omega), pow_add]
    calc 2 ^ padicValNat 2 (q ^ 2 - 1) * 2 ^ padicValNat 2 k ≤ 2 * (q + 1) * k :=
          Nat.mul_le_mul h2 (two_pow_padicValNat_le (by omega))
      _ = (q + 1) * (2 * k) := by ring
  · calc 2 ^ padicValNat 2 (q ^ j - 1) ≤ 2 ^ padicValNat 2 (q ^ 2 - 1) :=
          Nat.pow_le_pow_right (by norm_num) (padicValNat_pow_sub_one_le_of_odd hq hq1 hjo)
      _ ≤ 2 * (q + 1) := h2
      _ ≤ (q + 1) * j := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hj

theorem poly_sl_three (hq : 3 ≤ q) :
    (2 * (q ^ 2 - 1)) ^ 8 * (q - 1) ^ 3 ≤ (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ^ 3 := by
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 3 := ⟨q - 3, by omega⟩
  have h1 : 1 ≤ (t + 3) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (t + 3) ^ 3 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2, show 1 ≤ t + 3 by omega]
  have : (0 : ℤ) ≤ (((t : ℤ) + 3) ^ 3 * ((((t : ℤ) + 3) ^ 2 - 1) * (((t : ℤ) + 3) ^ 3 - 1))) ^ 3 -
      (2 * (((t : ℤ) + 3) ^ 2 - 1)) ^ 8 * (((t : ℤ) + 3) - 1) ^ 3 := by
    ring_nf
    positivity
  linarith

theorem poly_four (hq : 3 ≤ q) : ((q + 1) * 4) ^ 8 ≤ (q ^ 3 * (q ^ 4 - 1)) ^ 3 := by
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 3 := ⟨q - 3, by omega⟩
  have h1 : 1 ≤ (t + 3) ^ 4 := Nat.one_le_pow _ _ (by omega)
  zify [h1]
  have : (0 : ℤ) ≤ (((t : ℤ) + 3) ^ 3 * (((t : ℤ) + 3) ^ 4 - 1)) ^ 3 -
      (((t : ℤ) + 3 + 1) * 4) ^ 8 := by
    ring_nf
    positivity
  linarith

theorem poly_step (hq : 3 ≤ q) {j : ℕ} (hj : 4 ≤ j) :
    ((q + 1) * j) ^ 8 ≤ (q ^ (j - 1) * (q ^ j - 1)) ^ 3 := by
  induction j, hj using Nat.le_induction with
  | base => exact poly_four hq
  | succ j hj ih =>
    have h45 : 4 ^ 8 * ((q + 1) * (j + 1)) ^ 8 ≤ 5 ^ 8 * ((q + 1) * j) ^ 8 := by
      rw [← mul_pow, ← mul_pow]
      exact Nat.pow_le_pow_left (by nlinarith) 8
    have hqj : q * (q ^ j - 1) ≤ q ^ (j + 1) - 1 := by
      rw [Nat.mul_sub, mul_one, pow_succ, mul_comm (q ^ j)]
      omega
    have hge : q ^ 2 * (q ^ (j - 1) * (q ^ j - 1)) ≤ q ^ (j + 1 - 1) * (q ^ (j + 1) - 1) := by
      rw [Nat.add_sub_cancel]
      calc q ^ 2 * (q ^ (j - 1) * (q ^ j - 1)) = q ^ (j - 1 + 1) * (q * (q ^ j - 1)) := by ring
        _ ≤ q ^ (j - 1 + 1) * (q ^ (j + 1) - 1) := Nat.mul_le_mul_left _ hqj
        _ = q ^ j * (q ^ (j + 1) - 1) := by rw [Nat.sub_add_cancel (by omega)]
    have hq6 : 729 ≤ (q ^ 2) ^ 3 := by
      calc 729 = (3 ^ 2) ^ 3 := by norm_num
        _ ≤ (q ^ 2) ^ 3 := Nat.pow_le_pow_left (Nat.pow_le_pow_left hq 2) 3
    have hB : 729 * (q ^ (j - 1) * (q ^ j - 1)) ^ 3 ≤ (q ^ (j + 1 - 1) * (q ^ (j + 1) - 1)) ^ 3 :=
      calc 729 * (q ^ (j - 1) * (q ^ j - 1)) ^ 3
          ≤ (q ^ 2) ^ 3 * (q ^ (j - 1) * (q ^ j - 1)) ^ 3 := Nat.mul_le_mul_right _ hq6
        _ = (q ^ 2 * (q ^ (j - 1) * (q ^ j - 1))) ^ 3 := by ring
        _ ≤ _ := Nat.pow_le_pow_left hge 3
    have : 4 ^ 8 * ((q + 1) * (j + 1)) ^ 8 ≤ 4 ^ 8 * (q ^ (j + 1 - 1) * (q ^ (j + 1) - 1)) ^ 3 := by
      calc 4 ^ 8 * ((q + 1) * (j + 1)) ^ 8 ≤ 5 ^ 8 * ((q + 1) * j) ^ 8 := h45
        _ ≤ 5 ^ 8 * (q ^ (j - 1) * (q ^ j - 1)) ^ 3 := Nat.mul_le_mul_left _ ih
        _ ≤ 4 ^ 8 * (729 * (q ^ (j - 1) * (q ^ j - 1)) ^ 3) := by
          rw [← mul_assoc]
          exact Nat.mul_le_mul_right _ (by norm_num)
        _ ≤ _ := Nat.mul_le_mul_left _ hB
    exact Nat.le_of_mul_le_mul_left this (by norm_num)

theorem poly_sp_two (hq : 5 ≤ q) :
    (8 * (q + 1) ^ 2) ^ 8 ≤ 32 * (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) ^ 3 := by
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 5 := ⟨q - 5, by omega⟩
  have h1 : 1 ≤ (t + 5) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (t + 5) ^ 4 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2]
  have : (0 : ℤ) ≤ 32 * (((t : ℤ) + 5) ^ 4 * ((((t : ℤ) + 5) ^ 2 - 1) *
      (((t : ℤ) + 5) ^ 4 - 1))) ^ 3 - (8 * ((t : ℤ) + 5 + 1) ^ 2) ^ 8 := by
    ring_nf
    positivity
  linarith

theorem poly_sp_three (hq : 3 ≤ q) :
    (16 * (q + 1) ^ 3) ^ 8 ≤
      32 * (q ^ 9 * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1))) ^ 3 := by
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 3 := ⟨q - 3, by omega⟩
  have h1 : 1 ≤ (t + 3) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (t + 3) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ (t + 3) ^ 6 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2, h3]
  have : (0 : ℤ) ≤ 32 * (((t : ℤ) + 3) ^ 9 * ((((t : ℤ) + 3) ^ 2 - 1) *
      (((t : ℤ) + 3) ^ 4 - 1) * (((t : ℤ) + 3) ^ 6 - 1))) ^ 3 -
      (16 * ((t : ℤ) + 3 + 1) ^ 3) ^ 8 := by
    ring_nf
    positivity
  linarith

theorem poly_psl_two (hq : 17 ≤ q) : 8 * (q + 1) ^ 8 ≤ (q * (q ^ 2 - 1)) ^ 3 := by
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 17 := ⟨q - 17, by omega⟩
  have h1 : 1 ≤ (t + 17) ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h1]
  have : (0 : ℤ) ≤ (((t : ℤ) + 17) * (((t : ℤ) + 17) ^ 2 - 1)) ^ 3 -
      8 * ((t : ℤ) + 17 + 1) ^ 8 := by
    ring_nf
    positivity
  linarith

theorem poly_g2 (hq : 3 ≤ q) :
    (4 * (q + 1) ^ 2) ^ 8 ≤ (q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)) ^ 3 := by
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 3 := ⟨q - 3, by omega⟩
  have h1 : 1 ≤ (t + 3) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (t + 3) ^ 6 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2]
  have : (0 : ℤ) ≤ (((t : ℤ) + 3) ^ 6 * (((t : ℤ) + 3) ^ 6 - 1) * (((t : ℤ) + 3) ^ 2 - 1)) ^ 3 -
      (4 * ((t : ℤ) + 3 + 1) ^ 2) ^ 8 := by
    ring_nf
    positivity
  linarith

theorem poly_su3 (hq : 5 ≤ q) :
    27 * (2 * (q + 1) ^ 2) ^ 8 ≤ (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) ^ 3 := by
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 5 := ⟨q - 5, by omega⟩
  have h1 : 1 ≤ (t + 5) ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h1]
  have : (0 : ℤ) ≤ (((t : ℤ) + 5) ^ 3 * (((t : ℤ) + 5) ^ 2 - 1) * (((t : ℤ) + 5) ^ 3 + 1)) ^ 3 -
      27 * (2 * ((t : ℤ) + 5 + 1) ^ 2) ^ 8 := by
    ring_nf
    positivity
  linarith

theorem two_pow_padicValNat_su3_le (hq : Odd q) (hq1 : 1 < q) :
    2 ^ (padicValNat 2 (q ^ 2 - 1) + padicValNat 2 (q ^ 3 + 1)) ≤ 2 * (q + 1) ^ 2 := by
  rw [padicValNat_sq_sub_one hq hq1, padicValNat_pow_three_add_one hq]
  have hm := two_pow_padicValNat_le (n := q - 1) (by omega)
  have hp := two_pow_padicValNat_le (n := q + 1) (by omega)
  rcases padicValNat_sub_one_eq_one_or hq with h | h
  · rw [h, pow_add, pow_add, pow_one, mul_assoc, sq]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hp hp)
  · rw [h, show padicValNat 2 (q - 1) + 1 + 1 = padicValNat 2 (q - 1) + 2 by omega, pow_add]
    calc 2 ^ padicValNat 2 (q - 1) * 2 ^ 2 ≤ (q - 1) * 4 := Nat.mul_le_mul_right _ hm
      _ ≤ (q + 1) * (2 * (q + 1)) := Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * (q + 1) ^ 2 := by ring

theorem padicValNat_pow_four_sub_one (hq : Odd q) (hq1 : 1 < q) :
    padicValNat 2 (q ^ 4 - 1) = padicValNat 2 (q ^ 2 - 1) + 1 := by
  have h := padicValNat_pow_two_mul_sub_one hq hq1 (k := 2) two_ne_zero
  rwa [padicValNat.self one_lt_two] at h

theorem padicValNat_pow_six_sub_one (hq : Odd q) (hq1 : 1 < q) :
    padicValNat 2 (q ^ 6 - 1) = padicValNat 2 (q ^ 2 - 1) := by
  have h := padicValNat_pow_two_mul_sub_one hq hq1 (k := 3) (by norm_num)
  rwa [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3), add_zero] at h

theorem pow_sub_one_ne_zero (hq1 : 1 < q) {j : ℕ} (hj : j ≠ 0) : q ^ j - 1 ≠ 0 := by
  have : 1 < q ^ j := Nat.one_lt_pow hj hq1
  omega

theorem slOrd_pos (hq1 : 1 < q) (n : ℕ) :
    0 < q ^ (n * (n - 1) / 2) * ∏ j ∈ Icc 2 n, (q ^ j - 1) :=
  Nat.mul_pos (pow_pos (by omega) _) (prod_pos fun j hj =>
    Nat.pos_of_ne_zero (pow_sub_one_ne_zero hq1 (by simp at hj; omega)))

theorem slOrd_succ (q : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    q ^ ((n + 1) * (n + 1 - 1) / 2) * ∏ j ∈ Icc 2 (n + 1), (q ^ j - 1) =
      q ^ (n * (n - 1) / 2) * (∏ j ∈ Icc 2 n, (q ^ j - 1)) * (q ^ n * (q ^ (n + 1) - 1)) := by
  have he : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
    have : (n + 1) * (n + 1 - 1) = n * (n - 1) + 2 * n := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    rw [this, Nat.add_mul_div_left _ _ two_pos]
  rw [he, prod_Icc_succ_top (by omega), pow_add]
  ring

theorem two_pow_mul_le_slOrd (hq : Odd q) (hq3 : 3 ≤ q) {n : ℕ} (hn : 3 ≤ n) :
    2 ^ (8 * padicValNat 2 (q ^ (n * (n - 1) / 2) * ∏ j ∈ Icc 2 n, (q ^ j - 1))) * (q - 1) ^ 3 ≤
      (q ^ (n * (n - 1) / 2) * ∏ j ∈ Icc 2 n, (q ^ j - 1)) ^ 3 := by
  have hq1 : 1 < q := by omega
  induction n, hn using Nat.le_induction with
  | base =>
    have hprod : ∏ j ∈ Icc 2 3, (q ^ j - 1) = (q ^ 2 - 1) * (q ^ 3 - 1) := by
      rw [show Icc 2 3 = {2, 3} by rfl, prod_pair (by norm_num)]
    have h2 := pow_sub_one_ne_zero hq1 (j := 2) (by norm_num)
    have h3 := pow_sub_one_ne_zero hq1 (j := 3) (by norm_num)
    rw [show 3 * (3 - 1) / 2 = 3 by norm_num, hprod,
      padicValNat_odd_pow_mul hq _ (Nat.mul_ne_zero h2 h3), padicValNat.mul h2 h3, pow_mul']
    calc (2 ^ (padicValNat 2 (q ^ 2 - 1) + padicValNat 2 (q ^ 3 - 1))) ^ 8 * (q - 1) ^ 3
        ≤ (2 * (q ^ 2 - 1)) ^ 8 * (q - 1) ^ 3 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (two_pow_padicValNat_sl_three_le hq hq3) 8)
      _ ≤ _ := poly_sl_three hq3
  | succ n hn ih =>
    have hj := pow_sub_one_ne_zero hq1 (j := n + 1) (by omega)
    have hF : q ^ n * (q ^ (n + 1) - 1) ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ (by omega)) hj
    have hstep : 2 ^ (8 * padicValNat 2 (q ^ n * (q ^ (n + 1) - 1))) ≤
        (q ^ n * (q ^ (n + 1) - 1)) ^ 3 := by
      rw [padicValNat_odd_pow_mul hq _ hj, pow_mul']
      calc (2 ^ padicValNat 2 (q ^ (n + 1) - 1)) ^ 8 ≤ ((q + 1) * (n + 1)) ^ 8 :=
            Nat.pow_le_pow_left (two_pow_padicValNat_pow_sub_one_le hq hq1 (by omega)) 8
        _ ≤ (q ^ (n + 1 - 1) * (q ^ (n + 1) - 1)) ^ 3 := poly_step hq3 (by omega)
        _ = (q ^ n * (q ^ (n + 1) - 1)) ^ 3 := by rw [Nat.add_sub_cancel]
    rw [slOrd_succ q (by omega), padicValNat.mul (slOrd_pos hq1 n).ne' hF]
    calc 2 ^ (8 * (padicValNat 2 (q ^ (n * (n - 1) / 2) * ∏ j ∈ Icc 2 n, (q ^ j - 1)) +
          padicValNat 2 (q ^ n * (q ^ (n + 1) - 1)))) * (q - 1) ^ 3
        = (2 ^ (8 * padicValNat 2 (q ^ (n * (n - 1) / 2) * ∏ j ∈ Icc 2 n, (q ^ j - 1))) *
            (q - 1) ^ 3) * 2 ^ (8 * padicValNat 2 (q ^ n * (q ^ (n + 1) - 1))) := by ring
      _ ≤ (q ^ (n * (n - 1) / 2) * ∏ j ∈ Icc 2 n, (q ^ j - 1)) ^ 3 *
            (q ^ n * (q ^ (n + 1) - 1)) ^ 3 := Nat.mul_le_mul ih hstep
      _ = _ := by ring

theorem two_pow_le_of_mul_eq_slOrd (hq : Odd q) (hq3 : 3 ≤ q) {n N g : ℕ} (hn : 3 ≤ n)
    (hN : N * g = q ^ (n * (n - 1) / 2) * ∏ j ∈ Icc 2 n, (q ^ j - 1)) (hg : g ∣ q - 1) :
    2 ^ (8 * padicValNat 2 N) ≤ N ^ 3 := by
  have hA := slOrd_pos (by omega : 1 < q) n
  rw [← hN] at hA
  have hN0 : N ≠ 0 := by rintro rfl; simp at hA
  have hg0 : g ≠ 0 := by rintro rfl; simp at hA
  have hgq : g ≤ q - 1 := Nat.le_of_dvd (by omega) hg
  have h := two_pow_mul_le_slOrd hq hq3 hn
  rw [← hN, padicValNat.mul hN0 hg0] at h
  have : 2 ^ (8 * padicValNat 2 N) * g ^ 3 ≤ N ^ 3 * g ^ 3 :=
    calc 2 ^ (8 * padicValNat 2 N) * g ^ 3
        ≤ 2 ^ (8 * (padicValNat 2 N + padicValNat 2 g)) * (q - 1) ^ 3 :=
          Nat.mul_le_mul (Nat.pow_le_pow_right two_pos (by omega)) (Nat.pow_le_pow_left hgq 3)
      _ ≤ (N * g) ^ 3 := h
      _ = N ^ 3 * g ^ 3 := mul_pow _ _ _
  exact Nat.le_of_mul_le_mul_right this (pow_pos (Nat.pos_of_ne_zero hg0) 3)

theorem spOrd_pos (hq1 : 1 < q) (r : ℕ) :
    0 < q ^ (r ^ 2) * ∏ j ∈ Icc 1 r, (q ^ (2 * j) - 1) :=
  Nat.mul_pos (pow_pos (by omega) _) (prod_pos fun j hj =>
    Nat.pos_of_ne_zero (pow_sub_one_ne_zero hq1 (by simp at hj; omega)))

theorem spOrd_succ (q r : ℕ) :
    q ^ ((r + 1) ^ 2) * ∏ j ∈ Icc 1 (r + 1), (q ^ (2 * j) - 1) =
      q ^ (r ^ 2) * (∏ j ∈ Icc 1 r, (q ^ (2 * j) - 1)) *
        (q ^ (2 * (r + 1) - 1) * (q ^ (2 * (r + 1)) - 1)) := by
  rw [prod_Icc_succ_top (by omega), show (r + 1) ^ 2 = r ^ 2 + (2 * (r + 1) - 1) by
    rw [show 2 * (r + 1) - 1 = 2 * r + 1 by omega]; ring, pow_add]
  ring

theorem two_pow_le_spOrd (hq : Odd q) (hq3 : 3 ≤ q) {r : ℕ} (hr : 3 ≤ r ∨ r = 2 ∧ 5 ≤ q) :
    2 ^ (8 * padicValNat 2 (q ^ (r ^ 2) * ∏ j ∈ Icc 1 r, (q ^ (2 * j) - 1))) ≤
      32 * (q ^ (r ^ 2) * ∏ j ∈ Icc 1 r, (q ^ (2 * j) - 1)) ^ 3 := by
  have hq1 : 1 < q := by omega
  have he := two_pow_padicValNat_sq_sub_one_le hq hq1
  have h2 := pow_sub_one_ne_zero hq1 (j := 2) (by norm_num)
  have h4 := pow_sub_one_ne_zero hq1 (j := 4) (by norm_num)
  have h6 := pow_sub_one_ne_zero hq1 (j := 6) (by norm_num)
  have h24 := padicValNat_pow_four_sub_one hq hq1
  have h26 := padicValNat_pow_six_sub_one hq hq1
  rcases hr with hr | ⟨rfl, hq5⟩
  · induction r, hr using Nat.le_induction with
    | base =>
      have hprod : ∏ j ∈ Icc 1 3, (q ^ (2 * j) - 1) = (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) := by
        rw [show Icc 1 3 = {1, 2, 3} by rfl, prod_insert (by decide), prod_pair (by norm_num)]
        ring
      rw [show 3 ^ 2 = 9 by norm_num, hprod,
        padicValNat_odd_pow_mul hq _ (Nat.mul_ne_zero (Nat.mul_ne_zero h2 h4) h6),
        padicValNat.mul (Nat.mul_ne_zero h2 h4) h6, padicValNat.mul h2 h4, h24, h26, pow_mul']
      calc (2 ^ (padicValNat 2 (q ^ 2 - 1) + (padicValNat 2 (q ^ 2 - 1) + 1) +
            padicValNat 2 (q ^ 2 - 1))) ^ 8
          = (2 * (2 ^ padicValNat 2 (q ^ 2 - 1)) ^ 3) ^ 8 := by ring
        _ ≤ (2 * (2 * (q + 1)) ^ 3) ^ 8 :=
            Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left he 3)) 8
        _ = (16 * (q + 1) ^ 3) ^ 8 := by ring
        _ ≤ _ := poly_sp_three hq3
    | succ r hr ih =>
      have hj := pow_sub_one_ne_zero hq1 (j := 2 * (r + 1)) (by omega)
      have hF : q ^ (2 * (r + 1) - 1) * (q ^ (2 * (r + 1)) - 1) ≠ 0 :=
        Nat.mul_ne_zero (pow_ne_zero _ (by omega)) hj
      have hstep : 2 ^ (8 * padicValNat 2 (q ^ (2 * (r + 1) - 1) * (q ^ (2 * (r + 1)) - 1))) ≤
          (q ^ (2 * (r + 1) - 1) * (q ^ (2 * (r + 1)) - 1)) ^ 3 := by
        rw [padicValNat_odd_pow_mul hq _ hj, pow_mul']
        calc (2 ^ padicValNat 2 (q ^ (2 * (r + 1)) - 1)) ^ 8 ≤ ((q + 1) * (2 * (r + 1))) ^ 8 :=
              Nat.pow_le_pow_left (two_pow_padicValNat_pow_sub_one_le hq hq1 (by omega)) 8
          _ ≤ _ := poly_step hq3 (by omega)
      rw [spOrd_succ, padicValNat.mul (spOrd_pos hq1 r).ne' hF]
      calc 2 ^ (8 * (padicValNat 2 (q ^ (r ^ 2) * ∏ j ∈ Icc 1 r, (q ^ (2 * j) - 1)) +
            padicValNat 2 (q ^ (2 * (r + 1) - 1) * (q ^ (2 * (r + 1)) - 1))))
          = 2 ^ (8 * padicValNat 2 (q ^ (r ^ 2) * ∏ j ∈ Icc 1 r, (q ^ (2 * j) - 1))) *
              2 ^ (8 * padicValNat 2 (q ^ (2 * (r + 1) - 1) * (q ^ (2 * (r + 1)) - 1))) := by
            ring
        _ ≤ 32 * (q ^ (r ^ 2) * ∏ j ∈ Icc 1 r, (q ^ (2 * j) - 1)) ^ 3 *
              (q ^ (2 * (r + 1) - 1) * (q ^ (2 * (r + 1)) - 1)) ^ 3 := Nat.mul_le_mul ih hstep
        _ = _ := by ring
  · have hprod : ∏ j ∈ Icc 1 2, (q ^ (2 * j) - 1) = (q ^ 2 - 1) * (q ^ 4 - 1) := by
      rw [show Icc 1 2 = {1, 2} by rfl, prod_pair (by norm_num)]
    rw [show 2 ^ 2 = 4 by norm_num, hprod, padicValNat_odd_pow_mul hq _ (Nat.mul_ne_zero h2 h4),
      padicValNat.mul h2 h4, h24, pow_mul']
    calc (2 ^ (padicValNat 2 (q ^ 2 - 1) + (padicValNat 2 (q ^ 2 - 1) + 1))) ^ 8
        = (2 * (2 ^ padicValNat 2 (q ^ 2 - 1)) ^ 2) ^ 8 := by ring
      _ ≤ (2 * (2 * (q + 1)) ^ 2) ^ 8 :=
          Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left he 2)) 8
      _ = (8 * (q + 1) ^ 2) ^ 8 := by ring
      _ ≤ _ := poly_sp_two hq5

theorem two_pow_le_of_mul_two_eq_spOrd (hq : Odd q) (hq3 : 3 ≤ q) {r N : ℕ}
    (hr : 3 ≤ r ∨ r = 2 ∧ 5 ≤ q)
    (hN : N * 2 = q ^ (r ^ 2) * ∏ j ∈ Icc 1 r, (q ^ (2 * j) - 1)) :
    2 ^ (8 * padicValNat 2 N) ≤ N ^ 3 := by
  have hA := spOrd_pos (by omega : 1 < q) r
  rw [← hN] at hA
  have hN0 : N ≠ 0 := by rintro rfl; simp at hA
  have h := two_pow_le_spOrd hq hq3 hr
  rw [← hN, padicValNat.mul hN0 two_ne_zero, padicValNat.self one_lt_two] at h
  have : 2 ^ (8 * padicValNat 2 N) * 256 ≤ N ^ 3 * 256 :=
    calc 2 ^ (8 * padicValNat 2 N) * 256 = 2 ^ (8 * (padicValNat 2 N + 1)) := by ring
      _ ≤ 32 * (N * 2) ^ 3 := h
      _ = N ^ 3 * 256 := by ring
  exact Nat.le_of_mul_le_mul_right this (by norm_num)

theorem two_pow_le_of_mul_two_eq_psl_two (hq : Odd q) (hq1 : 1 < q) {N : ℕ}
    (hN : N * 2 = q * (q ^ 2 - 1)) (h6 : 6 ≤ padicValNat 2 N) :
    2 ^ (8 * padicValNat 2 N) ≤ N ^ 3 := by
  have h2 := pow_sub_one_ne_zero hq1 (j := 2) (by norm_num)
  have hN0 : N ≠ 0 := by
    rintro rfl
    have : 0 < q * (q ^ 2 - 1) := Nat.mul_pos (by omega) (Nat.pos_of_ne_zero h2)
    omega
  have hv : padicValNat 2 N + 1 = padicValNat 2 (q ^ 2 - 1) := by
    have h := congrArg (padicValNat 2) hN
    rw [padicValNat.mul hN0 two_ne_zero, padicValNat.self one_lt_two,
      show q * (q ^ 2 - 1) = q ^ 1 * (q ^ 2 - 1) by rw [pow_one],
      padicValNat_odd_pow_mul hq _ h2] at h
    exact h
  have hb : 2 ^ padicValNat 2 N ≤ q + 1 := by
    have := two_pow_padicValNat_sq_sub_one_le hq hq1
    rw [← hv, pow_succ] at this
    omega
  have hq17 : 17 ≤ q := by
    have : 2 ^ 6 ≤ 2 ^ padicValNat 2 N := Nat.pow_le_pow_right two_pos h6
    omega
  have : 8 * 2 ^ (8 * padicValNat 2 N) ≤ 8 * N ^ 3 :=
    calc 8 * 2 ^ (8 * padicValNat 2 N) = 8 * (2 ^ padicValNat 2 N) ^ 8 := by rw [pow_mul']
      _ ≤ 8 * (q + 1) ^ 8 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb 8)
      _ ≤ (q * (q ^ 2 - 1)) ^ 3 := poly_psl_two hq17
      _ = 8 * N ^ 3 := by rw [← hN]; ring
  omega

theorem two_pow_le_g2 (hq : Odd q) (hq3 : 3 ≤ q) :
    2 ^ (8 * padicValNat 2 (q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1))) ≤
      (q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)) ^ 3 := by
  have hq1 : 1 < q := by omega
  have h2 := pow_sub_one_ne_zero hq1 (j := 2) (by norm_num)
  have h6 := pow_sub_one_ne_zero hq1 (j := 6) (by norm_num)
  have he := two_pow_padicValNat_sq_sub_one_le hq hq1
  rw [mul_assoc, padicValNat_odd_pow_mul hq _ (Nat.mul_ne_zero h6 h2), padicValNat.mul h6 h2,
    padicValNat_pow_six_sub_one hq hq1, ← mul_assoc]
  calc 2 ^ (8 * (padicValNat 2 (q ^ 2 - 1) + padicValNat 2 (q ^ 2 - 1)))
      = ((2 ^ padicValNat 2 (q ^ 2 - 1)) ^ 2) ^ 8 := by ring
    _ ≤ ((2 * (q + 1)) ^ 2) ^ 8 := Nat.pow_le_pow_left (Nat.pow_le_pow_left he 2) 8
    _ = (4 * (q + 1) ^ 2) ^ 8 := by ring
    _ ≤ _ := poly_g2 hq3

theorem two_pow_le_of_mul_eq_su3 (hq : Odd q) (hq1 : 1 < q) {N g : ℕ}
    (hN : N * g = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) (hg : g ∣ 3) (h6 : 6 ≤ padicValNat 2 N) :
    2 ^ (8 * padicValNat 2 N) ≤ N ^ 3 := by
  have h2 := pow_sub_one_ne_zero hq1 (j := 2) (by norm_num)
  have h3 : q ^ 3 + 1 ≠ 0 := by omega
  have hg0 : g ≠ 0 := by rintro rfl; simp at hg
  have hg3 : g ≤ 3 := Nat.le_of_dvd (by norm_num) hg
  have hg2 : ¬ 2 ∣ g := fun h => absurd (h.trans hg) (by norm_num)
  have hS : 0 < q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) :=
    Nat.mul_pos (Nat.mul_pos (pow_pos (by omega) _) (Nat.pos_of_ne_zero h2)) (by omega)
  have hN0 : N ≠ 0 := by rintro rfl; omega
  have hv : padicValNat 2 N = padicValNat 2 (q ^ 2 - 1) + padicValNat 2 (q ^ 3 + 1) := by
    have h := congrArg (padicValNat 2) hN
    rw [padicValNat.mul hN0 hg0, padicValNat.eq_zero_of_not_dvd hg2, add_zero, mul_assoc,
      padicValNat_odd_pow_mul hq _ (Nat.mul_ne_zero h2 h3), padicValNat.mul h2 h3] at h
    exact h
  have hb : 2 ^ padicValNat 2 N ≤ 2 * (q + 1) ^ 2 := hv ▸ two_pow_padicValNat_su3_le hq hq1
  have hq5 : 5 ≤ q := by
    have : 2 ^ 6 ≤ 2 ^ padicValNat 2 N := Nat.pow_le_pow_right two_pos h6
    have : 32 ≤ (q + 1) ^ 2 := by omega
    nlinarith
  have : 2 ^ (8 * padicValNat 2 N) * g ^ 3 ≤ N ^ 3 * g ^ 3 :=
    calc 2 ^ (8 * padicValNat 2 N) * g ^ 3 ≤ (2 * (q + 1) ^ 2) ^ 8 * 27 := by
          rw [pow_mul']
          exact Nat.mul_le_mul (Nat.pow_le_pow_left hb 8)
            (by calc g ^ 3 ≤ 3 ^ 3 := Nat.pow_le_pow_left hg3 3
                  _ = 27 := by norm_num)
      _ ≤ (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) ^ 3 := by rw [mul_comm]; exact poly_su3 hq5
      _ = N ^ 3 * g ^ 3 := by rw [← hN, mul_pow]
  exact Nat.le_of_mul_le_mul_right this (pow_pos (Nat.pos_of_ne_zero hg0) 3)

end CFSG.RankThree.PartTwo.KFacts.OddChar
