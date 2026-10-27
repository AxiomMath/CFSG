module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG

namespace FiveTransitive.InvolutionSupportArithmetic

theorem degree_le_two_mul_support (n m i : ℕ)
    (hn : 4 ≤ n) (hm : 5 ≤ m) (hi : 2 ≤ i)
    (hmin : m ≤ 2 * i)
    (havg : (n - 4) * (i - 2) ≤ (m - 4) * (m - 2)) : n ≤ 2 * m := by
  have hn4 : n - 4 + 4 = n := by omega
  have hm4 : m - 4 + 4 = m := by omega
  have hm2 : m - 2 + 2 = m := by omega
  have hi2 : i - 2 + 2 = i := by omega
  have hleft : (n - 4) * (m - 4) ≤ (n - 4) * (2 * (i - 2)) := by
    apply Nat.mul_le_mul_left
    omega
  have hprod : (m - 4) * (n - 4) ≤ (m - 4) * (2 * (m - 2)) := by nlinarith
  have hcancel := Nat.le_of_mul_le_mul_left hprod (show 0 < m - 4 by omega)
  omega

end FiveTransitive.InvolutionSupportArithmetic

end CFSG
