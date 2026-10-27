module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.RankThree.PartOne.BRANCH

theorem two_pow_mod_three (f : ℕ) : (2 ^ f % 3 = 1 ∧ Even f) ∨ (2 ^ f % 3 = 2 ∧ Odd f) := by
  rcases Nat.even_or_odd' f with ⟨k, rfl | rfl⟩
  · left
    refine ⟨?_, ⟨k, by ring⟩⟩
    rw [pow_mul, Nat.pow_mod]
    norm_num
  · right
    refine ⟨?_, ⟨k, rfl⟩⟩
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num

theorem zmod_nine_cases_one {Q : ℕ} (h3 : Q % 3 = 1) :
    (Q : ZMod 9) = 1 ∨ (Q : ZMod 9) = 4 ∨ (Q : ZMod 9) = 7 := by
  have : Q % 9 = 1 ∨ Q % 9 = 4 ∨ Q % 9 = 7 := by omega
  rw [← ZMod.natCast_mod Q 9]
  rcases this with h | h | h <;> rw [h] <;> simp

theorem zmod_nine_cases_two {Q : ℕ} (h3 : Q % 3 = 2) :
    (Q : ZMod 9) = 2 ∨ (Q : ZMod 9) = 5 ∨ (Q : ZMod 9) = 8 := by
  have : Q % 9 = 2 ∨ Q % 9 = 5 ∨ Q % 9 = 8 := by omega
  rw [← ZMod.natCast_mod Q 9]
  rcases this with h | h | h <;> rw [h] <;> simp

theorem not_nine_dvd_g2_split {Q m : ℕ} (hQ : 2 ≤ Q) (h3 : Q % 3 = 1)
    (hm : (Q - 1) ^ 2 * m = Q ^ 6 * (Q ^ 6 - 1) * (Q ^ 2 - 1)) : ¬ 9 ∣ m := by
  have hQ1 : 1 ≤ Q := by omega
  have h6 : 1 ≤ Q ^ 6 := Nat.one_le_pow _ _ hQ1
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ1
  have hZ : ((Q : ℤ) - 1) ^ 2 * (m : ℤ) =
      (Q : ℤ) ^ 6 * ((Q : ℤ) ^ 6 - 1) * ((Q : ℤ) ^ 2 - 1) := by
    have := congrArg (Nat.cast : ℕ → ℤ) hm
    push_cast [Nat.cast_sub hQ1, Nat.cast_sub h6, Nat.cast_sub h2] at this
    exact this
  have hne : ((Q : ℤ) - 1) ^ 2 ≠ 0 := by
    have : (1 : ℤ) < Q := by exact_mod_cast hQ
    have : (Q : ℤ) - 1 ≠ 0 := by omega
    exact pow_ne_zero 2 this
  have hmZ : (m : ℤ) = (Q : ℤ) ^ 6 * ((Q : ℤ) + 1) ^ 2 * ((Q : ℤ) ^ 2 + Q + 1) *
      ((Q : ℤ) ^ 2 - Q + 1) := by
    apply mul_left_cancel₀ hne
    rw [hZ]
    ring
  intro h9
  have h9' : ((m : ℤ) : ZMod 9) = 0 := by
    rw [Int.cast_natCast]
    exact (ZMod.natCast_eq_zero_iff m 9).2 h9
  rw [hmZ] at h9'
  push_cast at h9'
  rcases zmod_nine_cases_one h3 with h | h | h <;> rw [h] at h9' <;> revert h9' <;> decide

theorem not_nine_dvd_g2_twisted {Q m : ℕ} (hQ : 2 ≤ Q) (h3 : Q % 3 = 2)
    (hm : (Q + 1) ^ 2 * m = Q ^ 6 * (Q ^ 6 - 1) * (Q ^ 2 - 1)) : ¬ 9 ∣ m := by
  have hQ1 : 1 ≤ Q := by omega
  have h6 : 1 ≤ Q ^ 6 := Nat.one_le_pow _ _ hQ1
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ1
  have hZ : ((Q : ℤ) + 1) ^ 2 * (m : ℤ) =
      (Q : ℤ) ^ 6 * ((Q : ℤ) ^ 6 - 1) * ((Q : ℤ) ^ 2 - 1) := by
    have := congrArg (Nat.cast : ℕ → ℤ) hm
    push_cast [Nat.cast_sub h6, Nat.cast_sub h2] at this
    exact this
  have hne : ((Q : ℤ) + 1) ^ 2 ≠ 0 := by positivity
  have hmZ : (m : ℤ) = (Q : ℤ) ^ 6 * ((Q : ℤ) - 1) ^ 2 * ((Q : ℤ) ^ 2 + Q + 1) *
      ((Q : ℤ) ^ 2 - Q + 1) := by
    apply mul_left_cancel₀ hne
    rw [hZ]
    ring
  intro h9
  have h9' : ((m : ℤ) : ZMod 9) = 0 := by
    rw [Int.cast_natCast]
    exact (ZMod.natCast_eq_zero_iff m 9).2 h9
  rw [hmZ] at h9'
  push_cast at h9'
  rcases zmod_nine_cases_two h3 with h | h | h <;> rw [h] at h9' <;> revert h9' <;> decide

theorem not_nine_dvd_triality_split {Q m : ℕ} (hQ : 2 ≤ Q) (h3 : Q % 3 = 1)
    (hm : ((Q ^ 3 - 1) * (Q - 1)) * m =
      Q ^ 12 * (Q ^ 2 - 1) * (Q ^ 6 - 1) * (Q ^ 8 + Q ^ 4 + 1)) : ¬ 9 ∣ m := by
  have hQ1 : 1 ≤ Q := by omega
  have h3' : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ hQ1
  have h6 : 1 ≤ Q ^ 6 := Nat.one_le_pow _ _ hQ1
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ1
  have hZ : (((Q : ℤ) ^ 3 - 1) * ((Q : ℤ) - 1)) * (m : ℤ) =
      (Q : ℤ) ^ 12 * ((Q : ℤ) ^ 2 - 1) * ((Q : ℤ) ^ 6 - 1) * ((Q : ℤ) ^ 8 + (Q : ℤ) ^ 4 + 1) := by
    have := congrArg (Nat.cast : ℕ → ℤ) hm
    push_cast [Nat.cast_sub hQ1, Nat.cast_sub h3', Nat.cast_sub h6, Nat.cast_sub h2] at this
    exact this
  have hQ2 : (1 : ℤ) < Q := by exact_mod_cast hQ
  have hne : ((Q : ℤ) ^ 3 - 1) * ((Q : ℤ) - 1) ≠ 0 := by
    have h1 : (Q : ℤ) - 1 ≠ 0 := by omega
    have h2 : (Q : ℤ) ^ 3 - 1 ≠ 0 := by
      have : (1 : ℤ) < (Q : ℤ) ^ 3 := one_lt_pow₀ hQ2 (by norm_num)
      omega
    exact mul_ne_zero h2 h1
  have hmZ : (m : ℤ) = (Q : ℤ) ^ 12 * ((Q : ℤ) ^ 8 + (Q : ℤ) ^ 4 + 1) * ((Q : ℤ) ^ 3 + 1) *
      ((Q : ℤ) + 1) := by
    apply mul_left_cancel₀ hne
    rw [hZ]
    ring
  intro h9
  have h9' : ((m : ℤ) : ZMod 9) = 0 := by
    rw [Int.cast_natCast]
    exact (ZMod.natCast_eq_zero_iff m 9).2 h9
  rw [hmZ] at h9'
  push_cast at h9'
  rcases zmod_nine_cases_one h3 with h | h | h <;> rw [h] at h9' <;> revert h9' <;> decide

theorem not_nine_dvd_triality_twisted {Q m : ℕ} (hQ : 2 ≤ Q) (h3 : Q % 3 = 2)
    (hm : ((Q + 1) * (Q ^ 3 + 1)) * m =
      Q ^ 12 * (Q ^ 2 - 1) * (Q ^ 6 - 1) * (Q ^ 8 + Q ^ 4 + 1)) : ¬ 9 ∣ m := by
  have hQ1 : 1 ≤ Q := by omega
  have h3' : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ hQ1
  have h6 : 1 ≤ Q ^ 6 := Nat.one_le_pow _ _ hQ1
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ1
  have hZ : (((Q : ℤ) + 1) * ((Q : ℤ) ^ 3 + 1)) * (m : ℤ) =
      (Q : ℤ) ^ 12 * ((Q : ℤ) ^ 2 - 1) * ((Q : ℤ) ^ 6 - 1) * ((Q : ℤ) ^ 8 + (Q : ℤ) ^ 4 + 1) := by
    have := congrArg (Nat.cast : ℕ → ℤ) hm
    push_cast [Nat.cast_sub h6, Nat.cast_sub h2] at this
    exact this
  have hne : ((Q : ℤ) + 1) * ((Q : ℤ) ^ 3 + 1) ≠ 0 := by positivity
  have hmZ : (m : ℤ) = (Q : ℤ) ^ 12 * ((Q : ℤ) ^ 8 + (Q : ℤ) ^ 4 + 1) * ((Q : ℤ) ^ 3 - 1) *
      ((Q : ℤ) - 1) := by
    apply mul_left_cancel₀ hne
    rw [hZ]
    ring
  intro h9
  have h9' : ((m : ℤ) : ZMod 9) = 0 := by
    rw [Int.cast_natCast]
    exact (ZMod.natCast_eq_zero_iff m 9).2 h9
  rw [hmZ] at h9'
  push_cast at h9'
  rcases zmod_nine_cases_two h3 with h | h | h <;> rw [h] at h9' <;> revert h9' <;> decide

theorem not_nine_dvd_ree_twisted {Q m : ℕ} (hQ : 2 ≤ Q) (h3 : Q % 3 = 2)
    (hm : (Q + 1) ^ 2 * m = Q ^ 12 * (Q - 1) ^ 2 * (Q + 1) ^ 2 * (Q ^ 2 + 1) ^ 2 *
      (Q ^ 2 - Q + 1) * (Q ^ 4 - Q ^ 2 + 1)) : ¬ 9 ∣ m := by
  have hQ1 : 1 ≤ Q := by omega
  have h2 : Q ≤ Q ^ 2 := Nat.le_self_pow (by norm_num) Q
  have h24 : Q ^ 2 ≤ Q ^ 4 := Nat.pow_le_pow_right hQ1 (by norm_num)
  have h2' : 1 ≤ Q ^ 2 - Q + 1 := by omega
  have hZ : ((Q : ℤ) + 1) ^ 2 * (m : ℤ) = (Q : ℤ) ^ 12 * ((Q : ℤ) - 1) ^ 2 * ((Q : ℤ) + 1) ^ 2 *
      ((Q : ℤ) ^ 2 + 1) ^ 2 * ((Q : ℤ) ^ 2 - Q + 1) * ((Q : ℤ) ^ 4 - (Q : ℤ) ^ 2 + 1) := by
    have := congrArg (Nat.cast : ℕ → ℤ) hm
    push_cast [Nat.cast_sub hQ1, Nat.cast_sub h2, Nat.cast_sub h24] at this
    exact this
  have hne : ((Q : ℤ) + 1) ^ 2 ≠ 0 := by positivity
  have hmZ : (m : ℤ) = (Q : ℤ) ^ 12 * ((Q : ℤ) - 1) ^ 2 * ((Q : ℤ) ^ 2 + 1) ^ 2 *
      ((Q : ℤ) ^ 2 - Q + 1) * ((Q : ℤ) ^ 4 - (Q : ℤ) ^ 2 + 1) := by
    apply mul_left_cancel₀ hne
    rw [hZ]
    ring
  intro h9
  have h9' : ((m : ℤ) : ZMod 9) = 0 := by
    rw [Int.cast_natCast]
    exact (ZMod.natCast_eq_zero_iff m 9).2 h9
  rw [hmZ] at h9'
  push_cast at h9'
  rcases zmod_nine_cases_two h3 with h | h | h <;> rw [h] at h9' <;> revert h9' <;> decide

end CFSG.RankThree.PartOne.BRANCH
