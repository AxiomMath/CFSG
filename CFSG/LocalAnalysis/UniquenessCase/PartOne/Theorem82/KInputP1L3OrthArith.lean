module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

private theorem mul_pred_add_two_mul {m : ℕ} (hm : 1 ≤ m) :
    m * (m - 1) + 2 * m = (m + 1) * m := by
  rw [Nat.mul_comm 2 m, ← Nat.mul_add, show m - 1 + 2 = m + 1 by omega, Nat.mul_comm]

theorem prod_four_pow_sub_one_lt {m : ℕ} (hm : 2 ≤ m) :
    ∏ i ∈ Finset.Icc 1 (m - 1), (4 ^ i - 1) < 2 ^ (m * (m - 1)) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [Finset.Icc_self, Finset.prod_singleton]
  | succ m hm ih =>
      have hprod : ∏ i ∈ Finset.Icc 1 ((m + 1) - 1), (4 ^ i - 1) =
          (∏ i ∈ Finset.Icc 1 (m - 1), (4 ^ i - 1)) * (4 ^ m - 1) := by
        rw [show (m + 1) - 1 = m by omega]
        rw [show m = (m - 1) + 1 by omega]
        rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ (m - 1) + 1)]
        rw [show (m - 1) + 1 = m by omega]
      rw [hprod, show (m + 1) - 1 = m by omega]
      calc (∏ i ∈ Finset.Icc 1 (m - 1), (4 ^ i - 1)) * (4 ^ m - 1)
          < 2 ^ (m * (m - 1)) * 4 ^ m :=
            Nat.mul_lt_mul'' ih (Nat.sub_lt (by positivity) (by norm_num))
        _ = 2 ^ (m * (m - 1)) * 2 ^ (2 * m) := by
              rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
        _ = 2 ^ (m * (m - 1) + 2 * m) := by rw [← pow_add]
        _ = 2 ^ ((m + 1) * m) := by
              rw [mul_pred_add_two_mul (m := m) (by omega : 1 ≤ m)]

private theorem add_two_le_two_mul {f m : ℕ} (hm : 4 ≤ m) (hfm : 3 * f = m * (m - 1)) :
    m + 2 ≤ 2 * f := by
  have h3 : 3 ≤ m - 1 := by omega
  have hmul1 : m * 3 ≤ m * (m - 1) := Nat.mul_le_mul_left m h3
  have h6m : 6 * m ≤ 2 * (m * (m - 1)) := by
    calc 6 * m = 2 * (m * 3) := by ring
      _ ≤ 2 * (m * (m - 1)) := Nat.mul_le_mul_left 2 hmul1
  have h3m : 3 * (m + 2) ≤ 6 * m := by omega
  have h6f : 3 * (m + 2) ≤ 6 * f := by
    calc 3 * (m + 2) ≤ 2 * (m * (m - 1)) := h3m.trans h6m
      _ = 6 * f := by rw [← hfm]; ring
  have h3' : 3 * (m + 2) ≤ 3 * (2 * f) := by omega
  exact Nat.le_of_mul_le_mul_left h3' (by norm_num)

private theorem orth_pow_lt_aux (X Y Z : ℕ) (hX : 16 ≤ X) (hY : 2 ≤ Y) (hZ : 4 * X ≤ Z) :
    (X + 1) * Y < (Z - 1) * (Y - 1) := by
  have hZ1 : 1 ≤ Z := by omega
  have hY1 : 1 ≤ Y := by omega
  have hX' : (16 : ℤ) ≤ (X : ℤ) := by exact_mod_cast hX
  have hY' : (2 : ℤ) ≤ (Y : ℤ) := by exact_mod_cast hY
  have hZ' : (4 : ℤ) * X ≤ (Z : ℤ) := by exact_mod_cast hZ
  have hgoal : ((X + 1) * Y : ℤ) < ((Z - 1) * (Y - 1) : ℤ) := by
    push_cast [Nat.cast_sub hZ1, Nat.cast_sub hY1]
    nlinarith
  exact_mod_cast hgoal

theorem orth_pow_lt {f m : ℕ} (hm : 4 ≤ m) (hfm : 3 * f = m * (m - 1)) :
    (2 ^ m + 1) * 2 ^ (m * (m - 1)) < ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) := by
  have h2f : m + 2 ≤ 2 * f := add_two_le_two_mul hm hfm
  have hY : 2 ≤ 2 ^ (m * (m - 1)) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (m * (m - 1)) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.mul_pos (by omega) (by omega))
  have hZ : 4 * 2 ^ m ≤ (2 ^ f) ^ 2 := by
    rw [show (2 ^ f) ^ 2 = 2 ^ (2 * f) by rw [← pow_mul, mul_comm]]
    calc 4 * 2 ^ m = 2 ^ (m + 2) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
          congr 1
          omega
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) h2f
  have hX : 16 ≤ 2 ^ m := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hm
  have hYeq : (2 ^ f) ^ 3 = 2 ^ (m * (m - 1)) := by
    rw [← pow_mul, mul_comm, hfm]
  have hmain := orth_pow_lt_aux (X := 2 ^ m) (Y := 2 ^ (m * (m - 1)))
    (Z := (2 ^ f) ^ 2) hX hY hZ
  simpa [hYeq] using hmain

theorem odd_two_pow_sub_one' {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  obtain ⟨j, hj⟩ : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have : 0 < 2 ^ k := by positivity
  exact ⟨j - 1, by omega⟩

theorem odd_two_pow_add_one' {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k + 1) := by
  obtain ⟨j, hj⟩ : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  exact ⟨j, by omega⟩

theorem prod_four_pow_sub_one_odd (m : ℕ) : Odd (∏ i ∈ Finset.Icc 1 (m - 1), (4 ^ i - 1)) := by
  refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun i hi => ?_
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  obtain ⟨k, hk⟩ : 4 ∣ 4 ^ i := dvd_pow_self 4 (by omega)
  have : 0 < 4 ^ i := by positivity
  exact ⟨2 * k - 1, by omega⟩

theorem factorization_two_pow_mul_odd {e c : ℕ} (hc : Odd c) :
    (2 ^ e * c).factorization 2 = e := by
  rw [Nat.factorization_mul (by positivity) hc.pos.ne', Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd hc.not_two_dvd_nat]
  simp

theorem two_pow_mul_odd_inj {s t a b : ℕ} (ha : Odd a) (hb : Odd b)
    (h : 2 ^ s * a = 2 ^ t * b) : s = t ∧ a = b := by
  have hst : s = t := by
    have := congrArg (fun n => n.factorization 2) h
    simpa only [factorization_two_pow_mul_odd ha, factorization_two_pow_mul_odd hb] using this
  subst hst
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩

theorem orth_odd_part_lt {m c : ℕ} (hm : 4 ≤ m) (hc : c ≤ 2 ^ m + 1) :
    c * ∏ i ∈ Finset.Icc 1 (m - 1), (4 ^ i - 1) < 2 ^ (2 * (m * (m - 1))) := by
  have hP := prod_four_pow_sub_one_lt (m := m) (by omega)
  have hN : m + 1 ≤ m * (m - 1) := by
    have : m * 3 ≤ m * (m - 1) := Nat.mul_le_mul_left m (by omega)
    omega
  have h2 : 2 ^ m + 1 ≤ 2 ^ (m * (m - 1)) := by
    calc 2 ^ m + 1 ≤ 2 ^ m + 2 ^ m := by have := Nat.one_le_two_pow (n := m); omega
      _ = 2 ^ (m + 1) := by ring
      _ ≤ 2 ^ (m * (m - 1)) := Nat.pow_le_pow_right (by norm_num) hN
  rcases Nat.eq_zero_or_pos c with rfl | hcpos
  · simp
  · calc c * ∏ i ∈ Finset.Icc 1 (m - 1), (4 ^ i - 1) < c * 2 ^ (m * (m - 1)) :=
          Nat.mul_lt_mul_of_pos_left hP hcpos
      _ ≤ 2 ^ (m * (m - 1)) * 2 ^ (m * (m - 1)) := by
          rw [mul_comm c]; exact Nat.mul_le_mul_left _ (hc.trans h2)
      _ = 2 ^ (2 * (m * (m - 1))) := by ring

theorem orth_order_ne {f m c d : ℕ} (hf : 1 ≤ f) (hm : 4 ≤ m)
    (hc : c = 2 ^ m - 1 ∨ c = 2 ^ m + 1) (hd : d = (2 ^ f) ^ 3 - 1 ∨ d = (2 ^ f) ^ 3 + 1) :
    (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * d) ≠
      2 ^ (m * (m - 1)) * c * ∏ i ∈ Finset.Icc 1 (m - 1), (4 ^ i - 1) := by
  intro h
  have hc1 : Odd c := by
    rcases hc with rfl | rfl
    exacts [odd_two_pow_sub_one' (by omega), odd_two_pow_add_one' (by omega)]
  have h8 : (2 ^ f) ^ 3 = 2 ^ (3 * f) := by rw [← pow_mul, mul_comm]
  have h4 : (2 ^ f) ^ 2 = 2 ^ (2 * f) := by rw [← pow_mul, mul_comm]
  have hd1 : Odd d := by
    rw [h8] at hd
    rcases hd with rfl | rfl
    exacts [odd_two_pow_sub_one' (by omega), odd_two_pow_add_one' (by omega)]
  have he1 : Odd ((2 ^ f) ^ 2 - 1) := by
    rw [h4]
    exact odd_two_pow_sub_one' (by omega)
  have hP := prod_four_pow_sub_one_odd m
  have h' : 2 ^ (3 * f) * (((2 ^ f) ^ 2 - 1) * d) =
      2 ^ (m * (m - 1)) * (c * ∏ i ∈ Finset.Icc 1 (m - 1), (4 ^ i - 1)) := by
    rw [← h8, h, mul_assoc]
  obtain ⟨h1, h2⟩ := two_pow_mul_odd_inj (he1.mul hd1) (hc1.mul hP) h'
  have hlt := orth_pow_lt hm h1
  have hPlt := prod_four_pow_sub_one_lt (m := m) (by omega)
  have hcle : c ≤ 2 ^ m + 1 := by
    rcases hc with rfl | rfl
    exacts [(Nat.sub_le _ _).trans (Nat.le_succ _), le_rfl]
  have hdge : (2 ^ f) ^ 3 - 1 ≤ d := by
    rcases hd with rfl | rfl
    exacts [le_rfl, (Nat.sub_le _ _).trans (Nat.le_succ _)]
  have hcP : c * ∏ i ∈ Finset.Icc 1 (m - 1), (4 ^ i - 1) ≤ (2 ^ m + 1) * 2 ^ (m * (m - 1)) :=
    Nat.mul_le_mul hcle hPlt.le
  have hed : ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) ≤ ((2 ^ f) ^ 2 - 1) * d :=
    Nat.mul_le_mul_left _ hdge
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
