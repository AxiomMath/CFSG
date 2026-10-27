module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG

namespace FiveTransitive.FourTransitiveSupportArithmetic

theorem degree_bound (n m : ℕ) (hm : 9 ≤ m)
    (hineq : m * (n - 2) * (n - 3) ≤
      2 * (n - 2) * (n - 3) + (m - 2) * (m - 1) * (n - 3) +
      (n - m) * (m - 2)^2 + (n - m) * (n - 3) +
      (m - 2) * (n - m - 1) * (m - 1)) : n ≤ 2 * m + 3 := by
  by_contra h
  let a := m - 9
  let k := n - (2 * m + 4)
  have hmEq : m = a + 9 := by dsimp [a]; omega
  have hnEq : n = 2 * a + k + 22 := by dsimp [a, k]; omega
  have hn2 : n - 2 = 2*a+k+20 := by omega
  have hn3 : n - 3 = 2*a+k+19 := by omega
  have hm2 : m - 2 = a+7 := by omega
  have hm1 : m - 1 = a+8 := by omega
  have hnm : n - m = a+k+13 := by omega
  have hnm1 : n - m - 1 = a+k+12 := by omega
  rw [hn2, hn3, hm2, hm1, hnm1, hnm, hmEq] at hineq
  have hpos : 0 < (a+6)*k^2 + (a^2+20*a+80)*k + (a^2+17*a+40) := by positivity
  nlinarith

end FiveTransitive.FourTransitiveSupportArithmetic

end CFSG
