module

public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGOrthNsSgnLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ≠ 2 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧ p ∣ 2 ^ lab.n + 1 ∧ 4 ≤ lab.rank

end CFSG.StandardType

end
