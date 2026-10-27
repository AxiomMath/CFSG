module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.NatFactorial

public section

namespace CFSG

namespace FiveTransitive.A9SmallActionArithmetic

theorem index_cases (n : ℕ) (hn : n ≤ 14) (hd : n ∣ 181440)
    (hb : 181440 ≤ n.factorial) : n = 9 ∨ n = 10 ∨ n = 12 ∨ n = 14 := by
  interval_cases n <;> norm_num [Nat.factorial] at *

end FiveTransitive.A9SmallActionArithmetic

end CFSG
