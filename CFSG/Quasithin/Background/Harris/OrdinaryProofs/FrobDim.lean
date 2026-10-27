module

public import CFSG.Quasithin.Background.Harris.L2.Setup

public section

namespace CFSG.Quasithin.Background.Harris.OrdinaryProofs

open CFSG.Quasithin.G11 CFSG.Quasithin.G11.Harris.L2 Matrix
open scoped MatrixGroups

theorem two_mul_le_two_pow {s : ℕ} (hs : 1 ≤ s) : 2 * s ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
    rw [pow_succ]
    have : 2 ≤ 2 ^ s := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
    omega

end CFSG.Quasithin.Background.Harris.OrdinaryProofs

end
