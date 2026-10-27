module

public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.RankThree.PartOne.Q1327S

theorem two_pow_mod_seven (g : ℕ) : 2 ^ g % 7 = 1 ∨ 2 ^ g % 7 = 2 ∨ 2 ^ g % 7 = 4 := by
  induction g with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h | h <;> simp [h]

theorem not_seven_dvd_two_pow_add_one (g : ℕ) : ¬ 7 ∣ 2 ^ g + 1 := by
  rcases two_pow_mod_seven g with h | h | h <;> omega

theorem ne_seven_of_dvd_two_pow_add_one {p g : ℕ} (h : p ∣ 2 ^ g + 1) : p ≠ 7 := by
  rintro rfl
  exact not_seven_dvd_two_pow_add_one g h

end CFSG.RankThree.PartOne.Q1327S
