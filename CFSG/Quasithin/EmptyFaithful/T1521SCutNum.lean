module

import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.T1521SCut

@[expose] def orderBound : ℕ := 145926144000

@[expose] def famOrders : List ℕ :=
  [60, 504, 4080, 32736, 262080, 2097024, 16776960, 134217216, 1073740800, 8589932544,
    68719472640, 168, 20160, 16482816, 1425715200, 62400, 5515776, 4279234560, 979200,
    1056706560, 29120, 32537600, 34093383680]

@[expose] def sporadicOrders : List ℕ :=
  [7920, 95040, 443520, 10200960, 244823040, 604800, 44352000, 4030387200, 145926144000]

theorem famOrders_ne_sporadic : ∀ m ∈ famOrders, ∀ s ∈ sporadicOrders, m ≠ s := by decide

theorem famOrders_pos : ∀ m ∈ famOrders, 0 < m := by decide

theorem famOrders_mul_two_pow : ∀ m ∈ famOrders, ∀ k < 40,
    m * 2 ^ k ≠ 6048 ∧ m * 2 ^ k ≠ 17971200 ∧ m * 2 ^ k ≠ 211341312 ∧ m * 2 ^ k ≠ 9999360 ∧
      (m * 2 ^ k = 20160 → m = 20160 ∧ k = 0) := by decide

theorem lt_forty_of_mul_two_pow {m k N : ℕ} (hm : 0 < m) (hN : N < 2 ^ 40)
    (h : m * 2 ^ k = N) : k < 40 := by
  by_contra hk
  push Not at hk
  have h1 : 2 ^ 40 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h2 : 2 ^ k ≤ m * 2 ^ k := Nat.le_mul_of_pos_left _ hm
  omega

theorem l2_le {n m : ℕ} (h : m + 2 ^ n = (2 ^ n) ^ 3) (hm : m ≤ orderBound) : n ≤ 12 := by
  by_contra hn
  push Not at hn
  have hq : 2 ^ 13 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hq2 : (2 ^ 13) ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2
  have h3 : 2 ^ n * (2 ^ 13) ^ 2 ≤ (2 ^ n) ^ 3 :=
    calc 2 ^ n * (2 ^ 13) ^ 2 ≤ 2 ^ n * (2 ^ n) ^ 2 := Nat.mul_le_mul_left _ hq2
      _ = (2 ^ n) ^ 3 := by ring
  unfold orderBound at hm
  norm_num at hq h3
  omega

theorem l3_le {n m g : ℕ} (hg : g ≤ 3)
    (h : m * g = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1))) (hm : m ≤ orderBound) :
    n ≤ 4 := by
  by_contra hn
  push Not at hn
  have hq : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h1 : (2 ^ 5) ^ 3 ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : (2 ^ 5) ^ 2 - 1 ≤ (2 ^ n) ^ 2 - 1 :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
  have h3 : (2 ^ 5) ^ 3 - 1 ≤ (2 ^ n) ^ 3 - 1 := Nat.sub_le_sub_right h1 1
  have h4 : (2 ^ 5) ^ 3 * (((2 ^ 5) ^ 2 - 1) * ((2 ^ 5) ^ 3 - 1)) ≤
      (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  have h6 : m * g ≤ orderBound * 3 := Nat.mul_le_mul hm hg
  unfold orderBound at h6
  norm_num at h4 h6
  omega

theorem u3_le {n m g : ℕ} (hg : g ≤ 3)
    (h : m * g = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1))) (hm : m ≤ orderBound) :
    n ≤ 4 := by
  by_contra hn
  push Not at hn
  have hq : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h1 : (2 ^ 5) ^ 3 ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : (2 ^ 5) ^ 2 - 1 ≤ (2 ^ n) ^ 2 - 1 :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
  have h3 : (2 ^ 5) ^ 3 + 1 ≤ (2 ^ n) ^ 3 + 1 := Nat.add_le_add_right h1 1
  have h4 : (2 ^ 5) ^ 3 * (((2 ^ 5) ^ 2 - 1) * ((2 ^ 5) ^ 3 + 1)) ≤
      (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  have h6 : m * g ≤ orderBound * 3 := Nat.mul_le_mul hm hg
  unfold orderBound at h6
  norm_num at h4 h6
  omega

theorem sp4_le {n m : ℕ} (h : m = (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)))
    (hm : m ≤ orderBound) : n ≤ 3 := by
  by_contra hn
  push Not at hn
  have hq : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h1 : (2 ^ 4) ^ 4 ≤ (2 ^ n) ^ 4 := Nat.pow_le_pow_left hq 4
  have h2 : (2 ^ 4) ^ 2 - 1 ≤ (2 ^ n) ^ 2 - 1 :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
  have h3 : (2 ^ 4) ^ 4 - 1 ≤ (2 ^ n) ^ 4 - 1 := Nat.sub_le_sub_right h1 1
  have h4 : (2 ^ 4) ^ 4 * (((2 ^ 4) ^ 2 - 1) * ((2 ^ 4) ^ 4 - 1)) ≤
      (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  unfold orderBound at hm
  norm_num at h4
  omega

theorem sz_le {a m : ℕ}
    (h : m = (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1))
    (hm : m ≤ orderBound) : a ≤ 3 := by
  by_contra hn
  push Not at hn
  have hq : 2 ^ 9 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : (2 ^ 9) ^ 2 ≤ (2 ^ (2 * a + 1)) ^ 2 := Nat.pow_le_pow_left hq 2
  have h2 : 2 ^ 9 - 1 ≤ 2 ^ (2 * a + 1) - 1 := Nat.sub_le_sub_right hq 1
  have h3 : (2 ^ 9) ^ 2 + 1 ≤ (2 ^ (2 * a + 1)) ^ 2 + 1 := Nat.add_le_add_right h1 1
  have h4 : (2 ^ 9) ^ 2 * (2 ^ 9 - 1) * ((2 ^ 9) ^ 2 + 1) ≤
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  unfold orderBound at hm
  norm_num at h4
  omega

theorem lt_lin2_order {n : ℕ} (h : 9 ≤ n) : 9999360 < 2 ^ n * (4 ^ n - 1) := by
  have h1 : 2 ^ 9 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
  have h2 : 4 ^ 9 - 1 ≤ 4 ^ n - 1 :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) h) 1
  have h3 := Nat.mul_le_mul h1 h2
  norm_num at h3
  omega

theorem lin2_order_ne {n : ℕ} (hn : 2 ≤ n) {N : ℕ}
    (hN : N = 2520 ∨ N = 168 ∨ N = 360 ∨ N = 6048 ∨ N = 20160 ∨ N = 9999360) :
    2 ^ n * (4 ^ n - 1) ≠ N := by
  intro h
  have hn9 : n < 9 := by
    by_contra h9
    push Not at h9
    have := lt_lin2_order h9
    omega
  interval_cases n <;> norm_num at h <;> omega

end CFSG.Quasithin.T1521SCut
