module

public import CFSG.LocalAnalysis.StandardType.GGTBRowSpDatum
public import CFSG.LocalAnalysis.StandardType.GGTBRowUDatum
public import CFSG.LocalAnalysis.StandardType.GGTBRowTwE6Datum
public import CFSG.LocalAnalysis.StandardType.GGTwE6BadDatum

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggExcReflTBWeylDatumQFourOn_of_rows
    (hRig : GGLabelRigidInput) {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGLabQFour p lab)
    (h : GGExcReflTBWeylDatumQFourOn fun p lab =>
      S p lab ∧ ¬ GGTBRowR3 p lab ∧ ¬ GGTBRowR6 p lab ∧ ¬ GGTBRowR5U p lab) :
    GGExcReflTBWeylDatumQFourOn S := by
  refine ggExcReflTBWeylDatumQFourOn_of_split S GGTBRowR3
    ((ggExcReflTBWeylDatumQFourOn_rowR3 hRig).mono fun p lab hl => ⟨hS p lab hl.1, hl.2⟩) ?_
  refine ggExcReflTBWeylDatumQFourOn_of_split (fun p lab => S p lab ∧ ¬ GGTBRowR3 p lab)
    GGTBRowR6
    ((ggExcReflTBWeylDatumQFourOn_rowR6 hRig).mono fun p lab hl => ⟨hS p lab hl.1.1, hl.2⟩) ?_
  refine ggExcReflTBWeylDatumQFourOn_of_split
    (fun p lab => (S p lab ∧ ¬ GGTBRowR3 p lab) ∧ ¬ GGTBRowR6 p lab) GGTBRowR5U
    (ggExcReflTBWeylDatumQFourOn_rowR5U.mono fun p lab hl => ⟨hS p lab hl.1.1.1, hl.2⟩) ?_
  exact h.mono fun p lab hl => ⟨hl.1.1.1, hl.1.1.2, hl.1.2, hl.2⟩

end CFSG.StandardType

end
