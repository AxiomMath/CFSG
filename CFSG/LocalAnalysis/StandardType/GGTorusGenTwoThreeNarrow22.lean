module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenTwoThreeNarrow22Defs
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpTwo
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOmegaPlusTwo
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOmegaMinusTwo
public import CFSG.LocalAnalysis.StandardType.GGTorusGenDThree
public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6SplitLabel
public import CFSG.LocalAnalysis.StandardType.GGTorusGenExcSplit
public import CFSG.LocalAnalysis.StandardType.GGTorusGenExcTwo
public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6Two
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTorusGen
public import CFSG.LocalAnalysis.StandardType.GGTorusGenTwoANarrow21
public import CFSG.LocalAnalysis.StandardType.GGTableBExcNarrow20
public import CFSG.LocalAnalysis.StandardType.GGTableBExcNarrow19
public import CFSG.LocalAnalysis.StandardType.GGTableBExcNarrow18
public import CFSG.LocalAnalysis.StandardType.GGCoverRkCoprimeNarrow17
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkCoprimeNarrow16
public import CFSG.LocalAnalysis.StandardType.GGCoverSLTwoNarrow15
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLDvdNarrow14
import CFSG.LocalAnalysis.StandardType.GGTorusGenUFour
import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthLabels
import CFSG.LocalAnalysis.StandardType.GGCoverPClassicalInner
import CFSG.LocalAnalysis.StandardType.GGCoverPSymplectic
import CFSG.LocalAnalysis.StandardType.GGCoverPOmegaPlus
import CFSG.LocalAnalysis.StandardType.GGCoverPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVac

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggL48TBForm1Rest20_of_rest22 (h : GGL48TBForm1Rest22) : GGL48TBForm1Rest20 := by
  intro p lab hp hlab hS hv hD4 h0 hA h2 hT hX hX2 hE hTw
  by_cases hD3 : GGL48TBDThreeRow p lab
  · exact CoverPInner.largeEvenLabelAll_coverP_DThree hp hD3.1 hD3.2.1 hD3.2.2
  by_cases hIn : GGL48TBForm1InnerRow p lab
  · exact CoverPInner.largeEvenLabelAll_coverP_inner hp (ggL48TBVac_ne_two_of_split hlab hS)
      hlab hIn.1 hIn.2 hD4
  by_cases hSp : GGTableBSympLabel p lab
  · exact CoverPSp.largeEvenLabelAll_coverP_symplectic hp hlab hSp
  by_cases hU4 : GGL48TBUFourRow p lab
  · exact largeEvenLabelAll_coverP_uFour hp hU4.1 hU4.2.1 hlab.1 hU4.2.2
  by_cases hO : GGTableBOrthSplitLabel p lab
  · rcases hO.1 with ht | ht
    · exact CoverPOmPlus.largeEvenLabelAll_coverP_omegaPlus hp ht hO.2.1 hO.2.2 hD4
    · exact CoverPOmMinus.largeEvenLabelAll_coverP_omegaMinus hp ht hO.2.1 hO.2.2
  exact h p lab hp hlab hS hv hD4 h0 hA h2 hT hX hX2 hE hTw hD3 hIn hSp hU4 hO

theorem ggL48TBForm4RestTwoA_of_restTwoThree
    (h : GGL48TBForm4RestTwoThree) :
    GGL48TBForm4RestTwoA := by
  intro p lab hp hlab hS hv h0 hA hT hU hE h2
  by_cases hB : GGSpTwoThreeLabel p lab
  · exact largeEvenLabelAll_torusGenTableB_spTwoThree hlab hB
  by_cases hDp : GGOmegaPlusTwoThreeLabel p lab
  · exact largeEvenLabelAll_torusGenTableB_omegaPlusTwoThree hDp
  by_cases hDm : GGOmegaMinusTwoThreeLabel p lab
  · exact largeEvenLabelAll_torusGenTableB_omegaMinusTwoThree hDm
  by_cases hD3 : GGL48TBDThreeRow p lab
  · exact largeEvenLabelAll_torusGenTableB_dThree hp hlab hD3.1 hD3.2.1 hD3.2.2
  by_cases hX : GGL48TBExcInnRow p lab
  · exact largeEvenLabelAll_torusGenTableB_excInn hp hlab hX
  by_cases hE6 : GGL48TBE6Row p lab
  · rcases eq_or_ne p 3 with rfl | h3
    · exact largeEvenLabelAll_torusGenTableB_E6_three hE6
    · exact largeEvenLabelAll_torusGenTableB_E6 hp h3 hlab hE6
  by_cases hU4 : GGL48TBUFourRow p lab
  · exact largeEvenLabelAll_torusGenTableB_uFour hp hU4.1 hU4.2.1 hlab.1 hU4.2.2
  by_cases hX2 : GGL48TBExcTwoRow p lab
  · rcases hX2.1 with h6 | h7 | h8 | h4
    · exact largeEvenLabelAll_torusGenTableB_e6Two hX2 h6
    · exact largeEvenLabelAll_torusGenTableB_excTwo hX2 (Or.inl h7)
    · exact largeEvenLabelAll_torusGenTableB_excTwo hX2 (Or.inr h8)
    · exact TableBF4TwoTB.largeEvenLabelAll_torusGenTableB_f4TwoThree_holds ⟨h4, hX2.2⟩
  by_cases hO : GGL48TBOrthRow p lab
  · exact largeEvenLabelAll_torusGenTableB_orth hp hO.1 hO.2.1 hO.2.2
  exact h p lab hp hlab hS hv h0 hA hT hU hE h2 hB hDp hDm hD3 hX hE6 hU4 hX2 hO

theorem ggL48TableBKnownFormsRestRkOpen21_of_open22
    (h : GGL48TableBKnownFormsRestRkOpen22) : GGL48TableBKnownFormsRestRkOpen21 :=
  ⟨ggL48TBForm1Rest20_of_rest22 h.1, ggL48TBForm4RestTwoA_of_restTwoThree h.2,
    ggL48TBForm5RowE_holds⟩

theorem ggL48TableBKnownFormsRestRkOpen13_of_open22
    (h : GGL48TableBKnownFormsRestRkOpen22) : GGL48TableBKnownFormsRestRkOpen13 := by
  have h21 := ggL48TableBKnownFormsRestRkOpen21_of_open22 h
  have h20 := ggL48TableBKnownFormsRestRkOpen20_of_open21 h21
  have h19 := ggL48TableBKnownFormsRestRkOpen19_of_open20 h20
  have h18 := ggL48TableBKnownFormsRestRkOpen18_of_open19 h19
  have h17 := ggL48TableBKnownFormsRestRkOpen17_of_open18 h18
  have h16 := ggL48TableBKnownFormsRestRkOpen16_of_open17 h17
  have h15 := ggL48TableBKnownFormsRestRkOpen15_of_open16 h16
  have h14 := ggL48TableBKnownFormsRestRkOpen14_of_open15 h15
  exact ggL48TableBKnownFormsRestRkOpen13_of_open14 h14

end CFSG.StandardType
