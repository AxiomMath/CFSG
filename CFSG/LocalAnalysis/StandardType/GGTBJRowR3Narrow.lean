module

public import CFSG.LocalAnalysis.StandardType.GGTBJSpRow
public import CFSG.LocalAnalysis.StandardType.GGTBJRowR4Narrow

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTBJNoncommReflOn_of_rowR3 (hRig : GGLabelRigidInput) {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGLabQFour p lab)
    (h : GGTBJNoncommReflOn fun p lab => S p lab ∧ ¬ GGTBRowR3 p lab) :
    GGTBJNoncommReflOn S :=
  ggTBJNoncommReflOn_of_split S GGTBRowR3
    ((ggTBJNoncommReflOn_of_naWeyl (ggTBJNaWeylQFourOn_rowR3 hRig)).mono
      fun p lab hl => ⟨hS p lab hl.1, hl.2⟩) h

end CFSG.StandardType

end
