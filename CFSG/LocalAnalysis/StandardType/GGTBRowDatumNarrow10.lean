module

public import CFSG.LocalAnalysis.StandardType.GGTBRowR1E6Three
public import CFSG.LocalAnalysis.StandardType.GGTwE6BadDatum

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggExcReflTBWeylDatumQFourOn_of_rowR1E6Three
    (hRig : GGLabelRigidInput) {S T : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGLabQFour p lab)
    (hT : ∀ p lab, GGLabQFour p lab → (lab.tag = .E6 ∧ p = 3) → T p lab)
    (hnc : GGTBJNoncommReflOn T)
    (h : GGExcReflTBWeylDatumQFourOn fun p lab => S p lab ∧ ¬ (lab.tag = .E6 ∧ p = 3)) :
    GGExcReflTBWeylDatumQFourOn S :=
  ggExcReflTBWeylDatumQFourOn_of_split S (fun p lab => (lab.tag = .E6 ∧ p = 3))
    (GGExcReflTBWeylDatumQFourOn.mono
      (ggExcReflTBWeylDatumQFourOn_rowR1E6Three hRig
        (GGTBJNoncommReflOn.mono hnc fun p lab hl => hT p lab hl.1 hl.2))
      fun p lab hl => ⟨hS p lab hl.1, hl.2⟩) h

end CFSG.StandardType

end
