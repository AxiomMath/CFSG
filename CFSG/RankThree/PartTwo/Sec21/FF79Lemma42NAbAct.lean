module

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.Abel
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Data.Finset.Range
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN

variable {A H : Type*} [AddCommGroup A] [Group H] [DistribMulAction H A]

theorem pow_mul_eq_of_mul_eq {σ c : H} (h : σ * c = c * σ ^ 4) (i : ℕ) :
    σ ^ i * c = c * σ ^ (4 * i) := by
  induction i with
  | zero => simp
  | succ n ih =>
    calc σ ^ (n + 1) * c = σ ^ n * (σ * c) := by rw [pow_succ, mul_assoc]
      _ = σ ^ n * (c * σ ^ 4) := by rw [h]
      _ = (σ ^ n * c) * σ ^ 4 := by rw [mul_assoc]
      _ = c * σ ^ (4 * (n + 1)) := by rw [ih, mul_assoc, ← pow_add]; ring_nf

theorem sq_mul_pow_eq {σ c : H} (h : σ * c = c * σ ^ 4) (i : ℕ) :
    (c * σ ^ i) ^ 2 = c ^ 2 * σ ^ (5 * i) := by
  calc (c * σ ^ i) ^ 2 = c * (σ ^ i * c) * σ ^ i := by rw [sq]; group
    _ = c * (c * σ ^ (4 * i)) * σ ^ i := by rw [pow_mul_eq_of_mul_eq h]
    _ = c ^ 2 * σ ^ (5 * i) := by
      rw [show c * (c * σ ^ (4 * i)) * σ ^ i = c ^ 2 * (σ ^ (4 * i) * σ ^ i) by
        simp only [sq, mul_assoc],
        ← pow_add, show 4 * i + i = 5 * i by ring]

theorem frob21_seven_smul {σ c : H} (hσ : σ ^ 7 = 1) (hsc : σ * c = c * σ ^ 4)
    (hN : ∀ i : ℕ, i < 7 → ∀ a : A, a + (c * σ ^ i) • a + ((c * σ ^ i) ^ 2) • a = 0)
    (a : A) : 7 • (σ • a) = 7 • a := by
  classical
  have hpm : ∀ n : ℕ, σ ^ n = σ ^ (n % 7) := fun n => pow_eq_pow_mod n hσ
  have e0 := hN 0 (by norm_num) (∑ j ∈ Finset.range 7, σ ^ j • a)
  have e1 := hN 0 (by norm_num) a
  have e2 := hN 1 (by norm_num) a
  have e3 := hN 2 (by norm_num) a
  have e4 := hN 3 (by norm_num) a
  have e5 := hN 4 (by norm_num) a
  have e6 := hN 5 (by norm_num) a
  have e7 := hN 6 (by norm_num) a
  simp only [sq_mul_pow_eq hsc] at e0 e1 e2 e3 e4 e5 e6 e7
  simp only [hpm (5 * 0), hpm (5 * 1), hpm (5 * 2), hpm (5 * 3), hpm (5 * 4), hpm (5 * 5),
    hpm (5 * 6)] at e1 e2 e3 e4 e5 e6 e7
  norm_num [Finset.sum_range_succ, smul_add, mul_smul, hpm 7] at e0 e1 e2 e3 e4 e5 e6 e7 ⊢
  have ht : σ • (a + σ • a + σ ^ 2 • a + σ ^ 3 • a + σ ^ 4 • a + σ ^ 5 • a + σ ^ 6 • a) =
      a + σ • a + σ ^ 2 • a + σ ^ 3 • a + σ ^ 4 • a + σ ^ 5 • a + σ ^ 6 • a := by
    have hs : ∀ k : ℕ, σ • σ ^ k • a = σ ^ (k + 1) • a := fun k => by
      rw [smul_smul, pow_succ']
    have hs1 : σ • σ • a = σ ^ 2 • a := by rw [smul_smul, sq]
    simp only [smul_add, hs1, hs 2, hs 3, hs 4, hs 5, hs 6]
    norm_num [hσ]
    abel
  have h7 : 7 • a = a + σ • a + σ ^ 2 • a + σ ^ 3 • a + σ ^ 4 • a + σ ^ 5 • a + σ ^ 6 • a := by
    have z : ((a + c • a + c ^ 2 • a) +
        (a + c • σ • a + c ^ 2 • σ ^ 5 • a) +
        (a + c • σ ^ 2 • a + c ^ 2 • σ ^ 3 • a) +
        (a + c • σ ^ 3 • a + c ^ 2 • σ • a) +
        (a + c • σ ^ 4 • a + c ^ 2 • σ ^ 6 • a) +
        (a + c • σ ^ 5 • a + c ^ 2 • σ ^ 4 • a) +
        (a + c • σ ^ 6 • a + c ^ 2 • σ ^ 2 • a)) -
        (a + σ • a + σ ^ 2 • a + σ ^ 3 • a + σ ^ 4 • a + σ ^ 5 • a + σ ^ 6 • a +
        (c • a + c • σ • a + c • σ ^ 2 • a + c • σ ^ 3 • a + c • σ ^ 4 • a + c • σ ^ 5 • a +
          c • σ ^ 6 • a) +
        (c ^ 2 • a + c ^ 2 • σ • a + c ^ 2 • σ ^ 2 • a + c ^ 2 • σ ^ 3 • a +
          c ^ 2 • σ ^ 4 • a + c ^ 2 • σ ^ 5 • a + c ^ 2 • σ ^ 6 • a)) = 0 := by
      rw [e1, e2, e3, e4, e5, e6, e7, e0]; simp
    exact sub_eq_zero.mp (by rw [← z]; abel)
  have hc : σ • (7 • a) = 7 • (σ • a) := (map_nsmul (DistribSMul.toAddMonoidHom A σ) 7 a)
  rw [← hc, h7, ht]

theorem a4_four_smul {c e1 e2 e3 : H} (he11 : e1 * e1 = 1) (he12 : e1 * e2 = e3)
    (he13 : e1 * e3 = e2) (h1 : (c * e1) ^ 2 = c ^ 2 * e2) (h2 : (c * e2) ^ 2 = c ^ 2 * e3)
    (h3 : (c * e3) ^ 2 = c ^ 2 * e1) (hN0 : ∀ a : A, a + c • a + (c ^ 2) • a = 0)
    (hN1 : ∀ a : A, a + (c * e1) • a + ((c * e1) ^ 2) • a = 0)
    (hN2 : ∀ a : A, a + (c * e2) • a + ((c * e2) ^ 2) • a = 0)
    (hN3 : ∀ a : A, a + (c * e3) • a + ((c * e3) ^ 2) • a = 0) (a : A) :
    4 • (e1 • a) = 4 • a := by
  have f0 := hN0 (a + e1 • a + e2 • a + e3 • a)
  have f1 := hN0 a
  have f2 := hN1 a
  have f3 := hN2 a
  have f4 := hN3 a
  rw [h1] at f2
  rw [h2] at f3
  rw [h3] at f4
  simp only [mul_smul, smul_add] at f0 f1 f2 f3 f4
  have ht : e1 • (a + e1 • a + e2 • a + e3 • a) = a + e1 • a + e2 • a + e3 • a := by
    simp only [smul_add, smul_smul, he11, he12, he13, one_smul]
    abel
  have h4 : 4 • a = a + e1 • a + e2 • a + e3 • a := by
    have z : ((a + c • a + c ^ 2 • a) + (a + c • e1 • a + c ^ 2 • e2 • a) +
        (a + c • e2 • a + c ^ 2 • e3 • a) + (a + c • e3 • a + c ^ 2 • e1 • a)) -
        (a + e1 • a + e2 • a + e3 • a + (c • a + c • e1 • a + c • e2 • a + c • e3 • a) +
          (c ^ 2 • a + c ^ 2 • e1 • a + c ^ 2 • e2 • a + c ^ 2 • e3 • a)) = 0 := by
      rw [f1, f2, f3, f4, f0]; simp
    exact sub_eq_zero.mp (by rw [← z]; abel)
  have hc : e1 • (4 • a) = 4 • (e1 • a) := (map_nsmul (DistribSMul.toAddMonoidHom A e1) 4 a)
  rw [← hc, h4, ht]

end CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN
