module

public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGFieldClassicalResidualLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ lab.rank = 2 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
    (lab.tag = .twA ∧ lab.rank = 2 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
    (lab.tag = .twA ∧ lab.rank = 4 ∧ p = 5 ∧ 5 ∣ 2 ^ lab.n + 1) ∨
    ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2 ∧ p = 3 ∧ lab.n = 3)

end CFSG.StandardType

end
