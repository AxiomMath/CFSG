module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXDetDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2InnerLabel (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twA ∧ 4 ≤ lab.rank ∧ ¬ 3 ∣ lab.rank + 1) ∨ lab.tag = .E7 ∨ lab.tag = .E8

end CFSG.StandardType

end
