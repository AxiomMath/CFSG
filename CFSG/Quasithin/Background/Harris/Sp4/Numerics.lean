module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.Quasithin.G11.Harris.Sp4

theorem eight_mul_le_four_pow' {s : ℕ} (hs : 2 ≤ s) : 8 * s ≤ 4 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
    rw [pow_succ]
    omega

theorem s_eq_one {f d s m : ℕ} (hfd : f ≤ s * d) (hdim : d * 4 ^ s ≤ 2 * (m + 1))
    (hm : m + 2 ≤ 4 * f) : s = 1 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    omega
  by_contra hs1
  have hs2 : 2 ≤ s := by omega
  have h8 := eight_mul_le_four_pow' hs2
  have : d * (8 * s) ≤ d * 4 ^ s := Nat.mul_le_mul_left d h8
  nlinarith

end CFSG.Quasithin.G11.Harris.Sp4
