module

public import CFSG.LocalAnalysis.StandardType.GGTBRowR1E7
public import CFSG.LocalAnalysis.StandardType.GGTwE6BadDatum

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggExcReflTBWeylDatumQFourOn_of_rowR1E7
    (hRig : GGLabelRigidInput) {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ _p lab, S _p lab → GGLabQFour _p lab)
    (h : GGExcReflTBWeylDatumQFourOn fun _p lab => S _p lab ∧ ¬ lab.tag = .E7) :
    GGExcReflTBWeylDatumQFourOn S :=
  ggExcReflTBWeylDatumQFourOn_of_split S (fun _p lab => lab.tag = .E7)
    (GGExcReflTBWeylDatumQFourOn.mono (ggExcReflTBWeylDatumQFourOn_rowR1E7 hRig)
      fun _p lab hl => ⟨hS _p lab hl.1, hl.2⟩) h

end CFSG.StandardType

end
