module

public import CFSG.LocalAnalysis.StandardType.GGTBRowR1AD
public import CFSG.LocalAnalysis.StandardType.GGTwE6BadDatum

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggExcReflTBWeylDatumQFourOn_of_rowR1AD
    (hRig : GGLabelRigidInput) {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGLabQFour p lab)
    (h : GGExcReflTBWeylDatumQFourOn fun p lab => S p lab ∧
      ¬ (((lab.tag = .A ∧ 3 ≤ lab.rank) ∧ ¬ p ∣ lab.rank + 1) ∨ lab.tag = .D)) :
    GGExcReflTBWeylDatumQFourOn S :=
  ggExcReflTBWeylDatumQFourOn_of_split S
    (fun p lab => ((lab.tag = .A ∧ 3 ≤ lab.rank) ∧ ¬ p ∣ lab.rank + 1) ∨ lab.tag = .D)
    (GGExcReflTBWeylDatumQFourOn.mono (ggExcReflTBWeylDatumQFourOn_rowR1AD hRig)
      fun p lab hl => ⟨hS p lab hl.1, hl.2⟩) h

end CFSG.StandardType

end
