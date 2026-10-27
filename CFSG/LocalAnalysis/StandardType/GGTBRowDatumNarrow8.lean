module

public import CFSG.LocalAnalysis.StandardType.GGTBRowR1E6
public import CFSG.LocalAnalysis.StandardType.GGTwE6BadDatum

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggExcReflTBWeylDatumQFourOn_of_rowR1E6Ne3
    (hRig : GGLabelRigidInput) {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGLabQFour p lab)
    (h : GGExcReflTBWeylDatumQFourOn fun p lab => S p lab ∧ ¬ (lab.tag = .E6 ∧ p ≠ 3)) :
    GGExcReflTBWeylDatumQFourOn S :=
  ggExcReflTBWeylDatumQFourOn_of_split S (fun p lab => (lab.tag = .E6 ∧ p ≠ 3))
    (GGExcReflTBWeylDatumQFourOn.mono (ggExcReflTBWeylDatumQFourOn_rowR1E6Ne3 hRig)
      fun p lab hl => ⟨hS p lab hl.1, hl.2⟩) h

end CFSG.StandardType

end
