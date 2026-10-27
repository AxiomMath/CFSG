module

public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGUnitDvdLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1

@[expose] def GGUnitDvd63Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGUnitDvdLabel p lab ∧ lab.rank = 5 ∧ p = 3

@[expose] def GGUnitDvdLabelNo63 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGUnitDvdLabel p lab ∧ ¬ (lab.rank = 5 ∧ p = 3)

end CFSG.StandardType

end
