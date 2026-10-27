module

public import CFSG.LocalAnalysis.StandardType.GGTBRowUDatum
public import CFSG.LocalAnalysis.StandardType.GGTBRowUdDatum
public import CFSG.LocalAnalysis.StandardType.GGTBRowBFrameDatum
public import CFSG.LocalAnalysis.StandardType.GGTBRowO2Datum
public import CFSG.LocalAnalysis.StandardType.GGTBRowVDatum
public import CFSG.LocalAnalysis.StandardType.GGTBRowR5Parity
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySp
public import CFSG.LocalAnalysis.StandardType.GGTBJRowR5Narrow
public import CFSG.LocalAnalysis.StandardType.GGTBRowDatumNarrow4

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggExcReflTBWeylDatumQFourOn_rowR5
    (hRig : GGLabelRigidInput) :
    GGExcReflTBWeylDatumQFourOn fun p lab => GGLabQFour p lab ∧ GGTBRowR5 p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hok hL
  have hcov : GGInnerDiagOnLabel (fun p lab =>
      (GGLabQFour p lab ∧ GGTBRowR5U p lab) ∨ (GGLabQFour p lab ∧ GGTBRowR5Ud p lab) ∨
      (GGLabQFour p lab ∧ GGTBRowR5O1 p lab) ∨ (GGLabQFour p lab ∧ GGTBRowR5O2 p lab) ∨
      (GGLabQFour p lab ∧ GGTBRowR5V p lab)) p Bs L :=
    (ggInnerDiagOnLabel_r5Par_of_rowR5 hRig hHyp hL).mono_label fun lab h => by
      obtain ⟨hq', hpar⟩ := h
      rcases ggTBRowR5Par_cases hpar with h | h | h | h | h
      · exact Or.inl ⟨hq', h⟩
      · exact Or.inr (Or.inl ⟨hq', h⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hq', h⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hq', h⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hq', h⟩)))
  intro hfact
  rcases hcov.elim_or with h | h
  · exact ggExcReflTBWeylDatumQFourOn_rowR5U G p B Bs x L D J hHyp hq hok h
  rcases h.elim_or with h | h
  · exact ggExcReflTBWeylDatumQFourOn_rowR5Ud
      (ggTBJNoncommReflOn_of_naWeyl ggTBJNaWeylQFourOn_rowR5Ud) G p B Bs x L D J hHyp hq hok h
  rcases h.elim_or with h | h
  · exact ggExcReflTBWeylDatumQFourOn_rowR5O1 G p B Bs x L D J hHyp hq hok h
  rcases h.elim_or with h | h
  · exact ggExcReflTBWeylDatumQFourOn_rowR5O2 G p B Bs x L D J hHyp hq hok h
  · exact ggExcReflTBWeylDatumQFourOn_rowR5V G p B Bs x L D J hHyp hq hok h

theorem ggExcReflTBWeylDatumQFourOn_of_rowR5
    (hRig : GGLabelRigidInput) {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGLabQFour p lab)
    (h : GGExcReflTBWeylDatumQFourOn fun p lab => S p lab ∧ ¬ GGTBRowR5 p lab) :
    GGExcReflTBWeylDatumQFourOn S :=
  ggExcReflTBWeylDatumQFourOn_of_split S GGTBRowR5
    ((ggExcReflTBWeylDatumQFourOn_rowR5 hRig).mono fun p lab hl => ⟨hS p lab hl.1, hl.2⟩) h

end CFSG.StandardType

end
