module

public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGOmegaMinusTwoThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  4 ≤ lab.rank ∧ lab.tag = .twD ∧ lab.n = 1 ∧ p = 3

end CFSG.StandardType
