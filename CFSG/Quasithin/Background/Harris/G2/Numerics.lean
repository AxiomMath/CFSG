module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Quasithin.G11.Harris.G2

theorem twelve_mul_le_six_pow {S : ℕ} (hS : 2 ≤ S) : 12 * S ≤ 6 ^ S := by
  induction S, hS using Nat.le_induction with
  | base => norm_num
  | succ S hS ih =>
    rw [pow_succ]
    omega

theorem one_of_numerics {f d S P : ℕ} (hd : 1 ≤ d) (hS : 1 ≤ S) (hfS : f ≤ S * d)
    (hP : 6 ^ S ≤ P) (hb : d * P ≤ 6 * f + 2) : S = 1 := by
  by_contra hne
  have hS2 : 2 ≤ S := by omega
  have h1 := twelve_mul_le_six_pow hS2
  have h2 : d * (12 * S) ≤ d * P := Nat.mul_le_mul_left d (h1.trans hP)
  nlinarith

end CFSG.Quasithin.G11.Harris.G2
