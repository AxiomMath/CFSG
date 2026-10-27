module

public import CFSG.LocalAnalysis.StandardType.GGTBRowO2Datum
public import CFSG.LocalAnalysis.StandardType.GGTBRowDatumNarrow2

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggExcReflTBWeylDatumQFourOn_of_rowR5O2
    {S : ℕ → LargeEvenLabel → Prop} (hS : ∀ p lab, S p lab → GGLabQFour p lab)
    (h : GGExcReflTBWeylDatumQFourOn fun p lab => S p lab ∧ ¬ GGTBRowR5O2 p lab) :
    GGExcReflTBWeylDatumQFourOn S :=
  ggExcReflTBWeylDatumQFourOn_of_split S GGTBRowR5O2
    (ggExcReflTBWeylDatumQFourOn_rowR5O2.mono fun p lab hl => ⟨hS p lab hl.1, hl.2⟩) h

end CFSG.StandardType

end
