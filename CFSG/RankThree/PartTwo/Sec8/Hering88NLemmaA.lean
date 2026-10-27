module

public import CFSG.Open.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88N

open CFSG.Open

theorem natCast_zmod_five_eq_zero {n : ℕ} (h : 5 ∣ n) : ((n : ℕ) : ZMod 5) = 0 := by
  obtain ⟨c, rfl⟩ := h; push_cast; rw [show (5 : ZMod 5) = 0 from rfl, zero_mul]

theorem five_not_dvd_ordTrialityD4 {k : ℕ} (hk : Odd k) : ¬ 5 ∣ ordTrialityD4 (2 ^ k) := by
  have hq : ((2 ^ k : ℕ) : ZMod 5) = 2 ∨ ((2 ^ k : ℕ) : ZMod 5) = 3 := by
    obtain ⟨j, rfl⟩ := hk
    push_cast
    rw [pow_succ, pow_mul, show (2 : ZMod 5) ^ 2 = -1 by decide]
    rcases neg_one_pow_eq_or (ZMod 5) j with h | h <;> rw [h] <;> decide
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  generalize 2 ^ k = q at hq h1
  intro h
  have h' := natCast_zmod_five_eq_zero h
  unfold ordTrialityD4 at h'
  push_cast [Nat.cast_sub (Nat.one_le_pow _ _ h1)] at h'
  generalize (q : ZMod 5) = x at hq h'
  rcases hq with rfl | rfl <;> revert h' <;> decide

theorem five_not_dvd_ordG2_cube {k : ℕ} (hk : Odd k) : ¬ 5 ∣ ordG2 (2 ^ (3 * k)) := by
  have hq : ((2 ^ (3 * k) : ℕ) : ZMod 5) = 2 ∨ ((2 ^ (3 * k) : ℕ) : ZMod 5) = 3 := by
    obtain ⟨j, rfl⟩ := hk
    push_cast
    rw [pow_mul, show (2 : ZMod 5) ^ 3 = 3 by decide, pow_succ, pow_mul,
      show (3 : ZMod 5) ^ 2 = -1 by decide]
    rcases neg_one_pow_eq_or (ZMod 5) j with h | h <;> rw [h] <;> decide
  have h1 : 1 ≤ 2 ^ (3 * k) := Nat.one_le_two_pow
  generalize 2 ^ (3 * k) = q at hq h1
  intro h
  have h' := natCast_zmod_five_eq_zero h
  unfold ordG2 at h'
  push_cast [Nat.cast_sub (Nat.one_le_pow _ _ h1)] at h'
  generalize (q : ZMod 5) = x at hq h'
  rcases hq with rfl | rfl <;> revert h' <;> decide

end CFSG.RankThree.PartTwo.Sec8.Hering88N
