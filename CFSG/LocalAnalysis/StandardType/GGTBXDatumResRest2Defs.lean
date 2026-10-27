module

public import CFSG.LocalAnalysis.StandardType.GGTwA5ThreeRestDefs
public import CFSG.LocalAnalysis.StandardType.GGPZNbrResRestDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTBResSmallLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ (lab.rank = 2 ∨ ((lab.rank = 3 ∨ lab.rank = 4) ∧ lab.n = 1 ∧ p = 3))) ∨
    (lab.tag = .twA ∧ lab.rank = 2) ∨ lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .triD4 ∨
    lab.tag = .twB2

@[expose] def GGTBWeylRowResRest2 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTBWeylRowResRest p lab ∧ ¬ GGTBResSmallLabel p lab

end CFSG.StandardType

end
