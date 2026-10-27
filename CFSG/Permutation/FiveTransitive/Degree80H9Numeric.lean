module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG

namespace FiveTransitive.Degree80H9Numeric

theorem invariant_cases (n t : ℕ)
    (hn : n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)
    (hlo : 1 ≤ t) (hhi : t ≤ 2) (hmod : n % 9 = t % 9) :
    (n = 2 ∧ t = 2) ∨ (n = 64 ∧ t = 1) := by
  omega

theorem three_not_dvd (n : ℕ)
    (hn : n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) : n % 3 ≠ 0 := by
  omega

end FiveTransitive.Degree80H9Numeric

end CFSG
