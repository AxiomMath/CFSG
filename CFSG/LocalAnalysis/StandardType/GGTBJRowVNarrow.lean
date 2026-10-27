module

public import CFSG.LocalAnalysis.StandardType.GGTBRowVDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJRowR4Narrow

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTBJNoncommReflOn_of_rowR5V
    {S : ℕ → LargeEvenLabel → Prop} (hS : ∀ p lab, S p lab → GGLabQFour p lab)
    (h : GGTBJNoncommReflOn fun p lab => S p lab ∧ ¬ GGTBRowR5V p lab) :
    GGTBJNoncommReflOn S :=
  ggTBJNoncommReflOn_of_split S GGTBRowR5V
    (ggTBJNoncommReflOn_rowR5V.mono fun p lab hl => ⟨hS p lab hl.1, hl.2⟩) h

end CFSG.StandardType

end
