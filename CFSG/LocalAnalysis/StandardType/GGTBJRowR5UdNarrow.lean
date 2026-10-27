module

public import CFSG.LocalAnalysis.StandardType.GGTBJSudRow
public import CFSG.LocalAnalysis.StandardType.GGTBJRowR4Narrow

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTBJNoncommReflOn_of_rowR5Ud
    {S : ℕ → LargeEvenLabel → Prop} (hS : ∀ p lab, S p lab → GGLabQFour p lab)
    (h : GGTBJNoncommReflOn fun p lab => S p lab ∧ ¬ GGTBRowR5Ud p lab) :
    GGTBJNoncommReflOn S :=
  ggTBJNoncommReflOn_of_split S GGTBRowR5Ud
    ((ggTBJNoncommReflOn_of_naWeyl ggTBJNaWeylQFourOn_rowR5Ud).mono
      fun p lab hl => ⟨hS p lab hl.1, hl.2⟩) h

end CFSG.StandardType

end
