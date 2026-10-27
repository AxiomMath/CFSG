module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG

theorem two_pow_mod_three_of_even {n : ℕ} (hn : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨m, rfl⟩ := hn
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [show m + 1 + (m + 1) = 2 * m + 2 by ring, pow_add, Nat.mul_mod,
      show 2 * m = m + m by ring, ih]
    norm_num

theorem two_pow_mod_three_of_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨m, rfl⟩ := hn
  induction m with
  | zero => norm_num
  | succ m ih =>
    have h : 2 * (m + 1) + 1 = 2 * m + 1 + 2 := by ring
    rw [h, pow_add, Nat.mul_mod, ih]
    norm_num

end CFSG
