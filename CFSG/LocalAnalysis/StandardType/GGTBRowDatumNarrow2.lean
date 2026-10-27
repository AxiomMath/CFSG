module

public import CFSG.LocalAnalysis.StandardType.GGTBRowBFrameDatum
public import CFSG.LocalAnalysis.StandardType.GGTBRowVDatum
public import CFSG.LocalAnalysis.StandardType.GGTwE6BadDatum

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggExcReflTBWeylDatumQFourOn_of_rows2
    {S : ℕ → LargeEvenLabel → Prop} (hS : ∀ p lab, S p lab → GGLabQFour p lab)
    (h : GGExcReflTBWeylDatumQFourOn fun p lab =>
      S p lab ∧ ¬ GGTBRowR5O1 p lab ∧ ¬ GGTBRowR5V p lab) :
    GGExcReflTBWeylDatumQFourOn S := by
  refine ggExcReflTBWeylDatumQFourOn_of_split S GGTBRowR5O1
    (ggExcReflTBWeylDatumQFourOn_rowR5O1.mono fun p lab hl => ⟨hS p lab hl.1, hl.2⟩) ?_
  refine ggExcReflTBWeylDatumQFourOn_of_split (fun p lab => S p lab ∧ ¬ GGTBRowR5O1 p lab)
    GGTBRowR5V
    (ggExcReflTBWeylDatumQFourOn_rowR5V.mono fun p lab hl => ⟨hS p lab hl.1.1, hl.2⟩) ?_
  exact h.mono fun p lab hl => ⟨hl.1.1, hl.1.2, hl.2⟩

end CFSG.StandardType

end
