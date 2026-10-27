module

public import CFSG.LocalAnalysis.WeakClosure81.W16Discharge
public import CFSG.LocalAnalysis.WeakClosure81.TwelveSchur
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenBar
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenDich
public import CFSG.LocalAnalysis.WeakClosure81.W16Mu2
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2False
import CFSG.LocalAnalysis.WeakClosure81.W16PFive
import CFSG.LocalAnalysis.WeakClosure81.W16PFiveFourteen
public import CFSG.LocalAnalysis.WeakClosure81.W19HoldsC
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenSmallCls
public import CFSG.LocalAnalysis.WeakClosure81.EightTailAssembly
public import CFSG.LocalAnalysis.WeakClosure81.TimTI.Main
import CFSG.LocalAnalysis.WeakClosure81.SpUCitedHolds
import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthHolds
import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfHolds
import CFSG.LocalAnalysis.WeakClosure81.W16LBorel
import CFSG.LocalAnalysis.WeakClosure81.W16LAutRank
import CFSG.LocalAnalysis.WeakClosure81.W16LRootFacts
import CFSG.LocalAnalysis.WeakClosure81.W16LU3Outer
import CFSG.LocalAnalysis.WeakClosure81.W16LPU3
import CFSG.LocalAnalysis.WeakClosure81.W16LSixCAssem
import CFSG.LocalAnalysis.WeakClosure81.W16POne
public import CFSG.LocalAnalysis.WeakClosure81.W16QDMain
public import CFSG.LocalAnalysis.WeakClosure81.W16QMain

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo

section Certified

variable {G : Type} [Group G] [Finite G]

theorem w3Lem86_1Two_of_cited
    (hCore : OddTranspositionCoreInputSCCls) (hList : OddTranspListBundleCls) :
    W3Lem86_1Two G := by
  have hTI : TimmesfeldTIRootInput := timmesfeldTIRootInput_holds
  have h711 : ∀ H : Subgroup G, W3Lem711Alt ↥H :=
    A6Case.w3Lem711Alt_subgroups_of_inputs hTI
      (CFSG.LocalAnalysis.WeakClosure81.SevenK.twoConjugateGeneration_of_suzukiSubgroupInput
          LieType.SuzukiSubgroups.suzukiSubgroupInput_holds) hCore.toInput hList.toInput
      orthReflParabolic_holds
  have hRU : SevenK.UnitaryRootCommutatorRank := unitaryRootCommutatorRank_holds
  have hRL : L2RootCommutatorRank := l2RootCommutatorRank_of_irreducible l2IrreducibleRank_holds
  have hP := w3Lem85ThreeFirst_and_shape_of_producers (G := G) spPSULieFacts_holds
    h711 hRU l2IrreducibleRank_holds orth6MinusOddTranspFact_holds spURootConfiguration_holds
  have hdisp : W3Lem85TwoDispatch G :=
    w3Lem85TwoDispatch_of_split h711 hRU hRL w3Lem85TwoGap1_holds w3Lem85TwoGap2_holds
      w3Lem85TwoGap3_holds w3Lem85TwoGap4_holds w3Lem85TwoGap5_holds
      (w3Lem85TwoGap6_of_fact orth6MinusOddTranspFact_holds)
  exact w3Lem86_1Two_of_kt_inputs (w3Lem85TwoKT_of_bad (w3Lem85TwoBad_of_dispatch hdisp))
    hP.1 hP.2.1 hP.2.2

private theorem w16l_sixI_of_std15 (hB : Asc80ThmB)
    (hCore : OddTranspositionCoreInputSCCls) (hList : OddTranspListBundleCls)
    (hS : Std15 G) : W16SixI G := by
  have hI : Inputs15Two G := Inputs15Two.of_inputs hB schurMultiplierInput
    (w3Lem86_1Two_of_cited hCore hList) w15Eleven3Dich_holds w15Eleven3S4_holds
    w15Eleven4Bar_holds
  have h152 : Thm152 G := thm152_of_inputs hI hS
  have h1 : W16One G := w16One_of_inputs timmesfeldTIRootInput_holds h152
  have h5 : W16Five G := w16Five_of_one h1 h152
  exact w16SixI_of_inputs spPSULieFacts_holds timmesfeldTIRootInput_holds
    (CFSG.LocalAnalysis.WeakClosure81.SevenK.twoConjugateGeneration_of_suzukiSubgroupInput
        LieType.SuzukiSubgroups.suzukiSubgroupInput_holds) hCore.toInput hList.toInput
    orthReflParabolic_holds h1 h5

theorem w3Thm162Gt2_of_cited (hB : Asc80ThmB)
    (hCore : OddTranspositionCoreInputSCCls) (hList : OddTranspListBundleCls) :
    W3Thm162Gt2 G := by
  intro D V₀ V h hV₀ hm
  have hI : Inputs15Two G := Inputs15Two.of_inputs hB schurMultiplierInput
    (w3Lem86_1Two_of_cited hCore hList) w15Eleven3Dich_holds w15Eleven3S4_holds
    w15Eleven4Bar_holds
  have h152 : Thm152 G := thm152_of_inputs hI (Std15.of_data D)
  have h1 : W16One G := w16One_of_inputs timmesfeldTIRootInput_holds h152
  have hSixI : W16SixI G := w16l_sixI_of_std15 hB hCore hList (Std15.of_data D)
  have h15 : W16Fifteen G := w16Fifteen_of_inputs hI.named h152 h1 hSixI
    (w16Fourteen_of_named_inputs hI.named) psuThreeRootFacts_holds perfectPSUThreeFact_holds
    psuThreeOuterInvolutionInput_holds
  have h5 : W16Five G := w16Five_of_one h1 h152
  exact w3Thm162Gt2_holds hI h1 h15
    (w16SixteenQ_holds h1 h5 h15
      (w16SixteenDich_holds h1 h5 h15 hSixI autRank166Input_holds kGroup1616Input_holds
        borel166Input_holds))
    (w16ClosingGt2_of_inputs timmesfeldTIRootInput_holds hCore.toInput hList.toInput
      orthReflParabolic_holds h1 h5 h15) D V₀ V h hV₀ hm

theorem w3Thm162MuTwo_of_cited (hB : Asc80ThmB)
    (hCore : OddTranspositionCoreInputSCCls) (hList : OddTranspListBundleCls) :
    W3Thm162MuTwo G := by
  intro D V₀ V h hx h61 hV₀ hm
  have hI : Inputs15Two G := Inputs15Two.of_inputs hB schurMultiplierInput
    (w3Lem86_1Two_of_cited hCore hList) w15Eleven3Dich_holds w15Eleven3S4_holds
    w15Eleven4Bar_holds
  have h152 : Thm152 G := thm152_of_inputs hI (Std15.of_data D)
  have h1 : W16One G := w16One_of_inputs timmesfeldTIRootInput_holds h152
  have hSixI : W16SixI G := w16l_sixI_of_std15 hB hCore hList (Std15.of_data D)
  have h15 : W16Fifteen G := w16Fifteen_of_inputs hI.named h152 h1 hSixI
    (w16Fourteen_of_named_inputs hI.named) psuThreeRootFacts_holds perfectPSUThreeFact_holds
    psuThreeOuterInvolutionInput_holds
  exact w3Thm162MuTwo_holds hI h1 h15 D V₀ V h hx h61 hV₀ hm

theorem w3Thm162Ext_of_cited (hB : Asc80ThmB)
    (hCore : OddTranspositionCoreInputSCCls) (hList : OddTranspListBundleCls) :
    W3Thm162Ext G :=
  W3Thm162Ext.of_gt2 (w3Thm162Gt2_of_cited hB hCore hList)
    (w3Thm162MuTwo_of_cited hB hCore hList)

theorem w3Thm193_of_cited (hB : Asc80ThmB)
    (hCore : OddTranspositionCoreInputSCCls) (hList : OddTranspListBundleCls) :
    W3Thm193 G :=
  w3Thm193_of_w3Thm162 (w3Thm162Gt2_of_cited hB hCore hList)

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
