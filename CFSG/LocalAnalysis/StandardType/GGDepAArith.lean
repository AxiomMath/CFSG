module

public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.StandardType

private lemma l05nDAA_lin_aux (j : ℕ) : j + 12 ≤ 5 ^ (j + 8) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have h1 : j + 1 + 12 = (j + 12) + 1 := by omega
    rw [h1]
    calc
      (j + 12) + 1 ≤ 5 * (j + 12) := by omega
      _ ≤ 5 * 5 ^ (j + 8) := Nat.mul_le_mul_left 5 ih
      _ = 5 ^ (j + 1 + 8) := by
            rw [show j + 1 + 8 = (j + 8) + 1 by omega, pow_succ]
            ring

private lemma l05nDAA_lin (k : ℕ) (hk : 8 ≤ k) : k + 4 ≤ 5 ^ k := by
  have h := l05nDAA_lin_aux (k - 8)
  have e1 : k - 8 + 12 = k + 4 := by omega
  have e2 : k - 8 + 8 = k := by omega
  rwa [e1, e2] at h

private lemma l05nDAA_exp (m : ℕ) (hm : 3 ≤ m) :
    (m - 1) * (m - 2) / 2 = (m - 2) * (m - 3) / 2 + (m - 2) := by
  have h1 : (m - 1).choose 2 = (m - 1) * (m - 2) / 2 := by
    rw [Nat.choose_two_right, show m - 1 - 1 = m - 2 by omega]
  have h2 : (m - 2).choose 2 = (m - 2) * (m - 3) / 2 := by
    rw [Nat.choose_two_right, show m - 2 - 1 = m - 3 by omega]
  have hkey : (m - 1).choose 2 = (m - 2).choose 2 + (m - 2) := by
    have h := Nat.choose_succ_succ (m - 2) 1
    have e : m - 2 + 1 = m - 1 := by omega
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd] at h
    rw [e, Nat.choose_one_right] at h
    rw [h]
    exact Nat.add_comm _ _
  rw [← h1, ← h2, hkey]

theorem ggDepA_order_ineq {p N : ℕ} (hp : 5 ≤ p) (hN : 11 ≤ N) :
    8 * (p ^ N * (6 * (p - 1) * Nat.factorial N)) < p ^ ((N - 2) * (N - 3) / 2) := by
  have hp0 : 0 < p := by omega
  refine Nat.le_induction (m := 11)
    (P := fun n _ => 8 * (p ^ n * (6 * (p - 1) * Nat.factorial n)) <
      p ^ ((n - 2) * (n - 3) / 2)) ?base ?step N hN
  · have hExp : (11 - 2) * (11 - 3) / 2 = 36 := by norm_num
    rw [hExp]
    have hX : 8 * (6 * (p - 1) * Nat.factorial 11) < p ^ 25 := by
      have hf : 48 * Nat.factorial 11 < 5 ^ 24 := by norm_num
      have hp1 : p - 1 < p := by omega
      calc
        8 * (6 * (p - 1) * Nat.factorial 11) = 48 * (p - 1) * Nat.factorial 11 := by
              ring
        _ < 48 * p * Nat.factorial 11 := by
              apply Nat.mul_lt_mul_of_pos_right
              · exact Nat.mul_lt_mul_of_pos_left hp1 (by norm_num)
              · norm_num
        _ = (48 * Nat.factorial 11) * p := by ring
        _ < 5 ^ 24 * p := Nat.mul_lt_mul_of_pos_right hf hp0
        _ ≤ p ^ 24 * p := Nat.mul_le_mul_right p (Nat.pow_le_pow_left hp 24)
        _ = p ^ 25 := by rw [← pow_succ]
    calc
      8 * (p ^ 11 * (6 * (p - 1) * Nat.factorial 11))
          = p ^ 11 * (8 * (6 * (p - 1) * Nat.factorial 11)) := by ring
      _ < p ^ 11 * p ^ 25 := Nat.mul_lt_mul_of_pos_left hX (pow_pos hp0 11)
      _ = p ^ 36 := by rw [← pow_add]
  · intro m hm ih
    have hexp : (m - 1) * (m - 2) / 2 = (m - 2) * (m - 3) / 2 + (m - 2) :=
      l05nDAA_exp m (by omega)
    have hbound : p * (m + 1) ≤ p ^ (m - 2) := by
      have hk8 : 8 ≤ m - 3 := by omega
      have hlin : m + 1 ≤ p ^ (m - 3) := by
        have h := l05nDAA_lin (m - 3) hk8
        have e : m - 3 + 4 = m + 1 := by omega
        rw [e] at h
        exact le_trans h (Nat.pow_le_pow_left hp (m - 3))
      calc
        p * (m + 1) ≤ p * p ^ (m - 3) := Nat.mul_le_mul_left p hlin
        _ = p ^ (m - 2) := by
              rw [mul_comm, ← pow_succ]
              congr 1
              omega
    have hident : 8 * (p ^ (m + 1) * (6 * (p - 1) * Nat.factorial (m + 1)))
        = (p * (m + 1)) * (8 * (p ^ m * (6 * (p - 1) * Nat.factorial m))) := by
      rw [pow_succ, Nat.factorial_succ]
      ring
    calc
      8 * (p ^ (m + 1) * (6 * (p - 1) * Nat.factorial (m + 1)))
          = (p * (m + 1)) * (8 * (p ^ m * (6 * (p - 1) * Nat.factorial m))) := hident
      _ < (p * (m + 1)) * p ^ ((m - 2) * (m - 3) / 2) :=
            Nat.mul_lt_mul_of_pos_left ih (Nat.mul_pos hp0 (by omega))
      _ ≤ p ^ (m - 2) * p ^ ((m - 2) * (m - 3) / 2) :=
            Nat.mul_le_mul_right _ hbound
      _ = p ^ ((m - 2) + (m - 2) * (m - 3) / 2) := by rw [← pow_add]
      _ = p ^ (((m + 1) - 2) * ((m + 1) - 3) / 2) := by
            congr 1
            have h1 : (m + 1) - 2 = m - 1 := by omega
            have h2 : (m + 1) - 3 = m - 2 := by omega
            rw [h1, h2, hexp]
            ring

end CFSG.StandardType
