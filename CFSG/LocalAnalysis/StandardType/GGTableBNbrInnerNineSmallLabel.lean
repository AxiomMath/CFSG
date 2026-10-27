module

public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGTableBNbrInnerNineSmallLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2 ∨ lab.tag = .G2der ∨ lab.tag = .twF4der ∨ lab.tag = .B2der ∨ lab.tag = .twB2 ∨
    (lab.tag = .A ∧ lab.rank = 2) ∨ (lab.tag = .triD4 ∧ (p = 3 ∨ p ∣ (2 ^ lab.n) ^ 2 - 1)) ∨
    (lab.tag = .twF4 ∧ p ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twA ∧ lab.rank = 2)

end CFSG.StandardType
