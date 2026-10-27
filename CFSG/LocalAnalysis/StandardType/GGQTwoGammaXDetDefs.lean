module

public import CFSG.LocalAnalysis.StandardType.GGQTwoI1FailGlue
public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2DetLabel (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twA ∧ 3 ∣ lab.rank + 1) ∨ lab.tag = .twE6

@[expose] def GGQ2TBMarked {G : Type} [Group G] (p : ℕ) (L : Subgroup G) (lab : LargeEvenLabel) :
    Prop :=
  GGLabQTwo p lab ∧ GGQ2TBLabel lab ∧ LargeEvenMarking L (fun lab' _ _ _ _ _ => lab' = lab)

end CFSG.StandardType

end
