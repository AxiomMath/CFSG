module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkNarrowDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkLabels
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBScWeyl
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBBridgeLabels
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48RkF4Irred
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem largeEvenLabelAll_irredModTableB_spSplit {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGTableBSympLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGIrredModTableB p R I ∨ GGWPlusTableB p R I :=
  largeEvenLabelAll_irredModTableB_of_torusIrred hp
    ((SpModel.largeEvenLabelAll_weylInputs_symplectic hp hlab h).mono
      fun _ _ _ _ ⟨r, hl, _, hi, _⟩ => ⟨r, hl, hi⟩)

theorem ggL48TableBKnownFormsRestRk_of_open
    (h : GGL48TableBKnownFormsRestRkOpen) : GGL48TableBKnownFormsRestRk := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h8⟩ := h
  unfold GGL48TableBKnownFormsRestRk
  refine ⟨h1, h2, h3, h4, h5, ?_, ggL48IrredModRkF4Two_holds, h8⟩
  intro p lab hp hlab hs hv hd hf ht
  rcases ggL48_irred_labels_exhaustive hp hlab hs hv hd hf ht with hc | hsp | hln | ho
  · exact ggL48IrredModOrWPlus_covered hp hlab hc
  · exact largeEvenLabelAll_irredModTableB_spSplit hp hlab hsp
  · exact largeEvenLabelAll_irredModTableB_linearNs hp hlab hln
  · exact h6 p lab hp hlab hs hv hd hf ht ho

end CFSG.StandardType
