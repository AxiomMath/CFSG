module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.NatFactorial

public section

namespace CFSG

namespace FiveTransitive.A9TenQuotientArithmetic

theorem factorial_product_lt (n k : ℕ) (hn : n ≤ 10) (hk : 2 ≤ k) (hk8 : k ≤ 8) :
    k.factorial * (n - k).factorial < 181440 := by
  have hb := Nat.factorial_le (Nat.sub_le_sub_right hn k)
  have hm := Nat.mul_le_mul_left k.factorial hb
  apply lt_of_le_of_lt hm
  interval_cases k <;> norm_num [Nat.factorial]

end FiveTransitive.A9TenQuotientArithmetic

end CFSG
