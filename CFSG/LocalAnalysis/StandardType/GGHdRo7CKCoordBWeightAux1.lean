module

public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Bound.Init
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.StandardType.HdRo7C

lemma hdRo7CKCoordAux_ite_one_inj : ∀ (c d : ZMod 3), c ≠ 0 → d ≠ 0 →
    (if c = 1 then (0 : Fin 2) else 1) = (if d = 1 then 0 else 1) → c = d := by
  decide

lemma hdRo7CKCoordAux_swap_symm_apply_left {α : Type*} [DecidableEq α] (i j : α) :
    (Equiv.swap i j).symm j = i := by
  rw [Equiv.symm_apply_eq]
  exact (Equiv.swap_apply_left i j).symm

lemma hdRo7CKCoordAux_swap_symm_apply_of_ne {α : Type*} [DecidableEq α] (i j x : α)
    (h1 : x ≠ i) (h2 : x ≠ j) : (Equiv.swap i j).symm x = x := by
  rw [Equiv.symm_apply_eq]
  exact (Equiv.swap_apply_of_ne_of_ne h1 h2).symm

lemma hdRo7CKCoordAux_single_eq_smul {n : ℕ} (k : Fin n) (c : ZMod 3) :
    Pi.single k c = c • (Pi.single k (1 : ZMod 3)) := by
  ext l
  by_cases hl : l = k
  · subst hl; simp [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne hl]

lemma hdRo7CKCoordAux_arith_step {n t : ℕ} (h2 : 2 ≤ t) (ht : t + 2 ≤ n) :
    (n - t) * 2 ^ t ≤ (n - (t + 1)) * 2 ^ (t + 1) := by
  have hnt : n - t = (n - (t + 1)) + 1 := by omega
  have hle : (n - (t + 1)) + 1 ≤ 2 * (n - (t + 1)) := by omega
  calc
    (n - t) * 2 ^ t = ((n - (t + 1)) + 1) * 2 ^ t := by rw [hnt]
    _ ≤ (2 * (n - (t + 1))) * 2 ^ t := Nat.mul_le_mul_right _ hle
    _ = (n - (t + 1)) * 2 ^ (t + 1) := by rw [pow_succ]; ring

lemma hdRo7CKCoordAux_arith_aux {n d : ℕ} (hn : 5 ≤ n) (hd : 2 + d ≤ n - 1) :
    4 * (n - 2) ≤ (n - (2 + d)) * 2 ^ (2 + d) := by
  induction d with
  | zero => exact le_of_eq (mul_comm 4 (n - 2))
  | succ d ih =>
      have hd' : 2 + d ≤ n - 1 := by omega
      have hstep : (n - (2 + d)) * 2 ^ (2 + d) ≤
          (n - (2 + d + 1)) * 2 ^ (2 + d + 1) :=
        hdRo7CKCoordAux_arith_step (n := n) (t := 2 + d) (by omega) (by omega)
      exact le_trans (ih hd') hstep

lemma hdRo7CKCoordAux_arith_lin {n : ℕ} (hn : 5 ≤ n) : 2 * n < 4 * (n - 2) := by omega

lemma hdRo7CKCoordAux_key1 {n t : ℕ} (hn : 5 ≤ n) (h2 : 2 ≤ t) (ht : t ≤ n - 1) :
    2 * n < (n - t) * 2 ^ t := by
  have hd : 2 + (t - 2) ≤ n - 1 := by omega
  have haux : 4 * (n - 2) ≤ (n - (2 + (t - 2))) * 2 ^ (2 + (t - 2)) :=
    hdRo7CKCoordAux_arith_aux hn hd
  have ht' : 2 + (t - 2) = t := by omega
  rw [ht'] at haux
  exact lt_of_lt_of_le (hdRo7CKCoordAux_arith_lin hn) haux

lemma hdRo7CKCoordAux_arith_key2_aux {n : ℕ} (hn : 3 ≤ n) : 2 * n < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      rw [hpow]
      nlinarith [ih, hk]

lemma hdRo7CKCoordAux_key2 {n : ℕ} (hn : 5 ≤ n) : 2 * n < 2 ^ n :=
  hdRo7CKCoordAux_arith_key2_aux (by omega)

end CFSG.StandardType.HdRo7C

end
