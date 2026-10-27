module

public import CFSG.LocalAnalysis.StandardType.GGIOneExcE6
public import CFSG.LocalAnalysis.StandardType.GGIOneExcTwE6
public import CFSG.LocalAnalysis.StandardType.GGIOneExcSmall
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveMain
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoMain
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnAll
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnTwDMain
public import CFSG.LocalAnalysis.StandardType.GGOPlusEightTwoMain
public import CFSG.LocalAnalysis.StandardType.GGOPlusEightTwoCommute

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Certs

theorem ggStdSubIOneProperInputOn_exc_of_inputs
    (hE6 : GGE6ThreeRankSixTwoLocal) (hX6 : GGE6InnerDiagBoundThreeInput)
    (hO6 : GGE6OuterThreeInput) (hE7 : GGE7TwoRootAsInput) (hE8 : GGE8TwoRootAsInput)
    (hF4 : GGF4TwoRootAsInput) (hC : GGExcTwoCenterThreeInput)
    (hTX : GGTwE6InnerDiagBound2LInput) (hTR : GGTwE6RootAsInnInput)
    (hTR3 : GGTwE6RootAsInnThreeInput) (hTD3 : GGTwE6DeltaInput3)
    (hTC : GGTwE6CenterPrimeInput) (hTO : GGTwE6OuterPowInput) :
    GGStdSubIOneProperInputOn GGIOneRestFiveExcLabel :=
  ggStdSubIOneProperInputOn_of_labels ggLNoncyclicInput_holds fun p lab hp hlab hS _ => by
    rcases hS with ⟨ht, hn1, rfl⟩ | ⟨ht, hdvd⟩ | ⟨ht, rfl, hdvd⟩
    · rcases ht with ht | ht | ht
      · exact ggIE_labelAll_E7Two hE7 hC ht hn1
      · exact ggIE_labelAll_E8Two hE8 hC ht hn1
      · exact ggIE_labelAll_F4Two hF4 hC ht hn1
    · exact ggIE_labelAll_twE6 hTX hTR hTR3 hTD3 hTC hTO hp ht hlab hdvd
    · exact ggIE_labelAll_E6_three hE6 hX6 hO6 ht hlab hdvd

end Certs

end CFSG.StandardType

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG CFSG.Assembly CFSG.StandardType

theorem ggRemainderStdSubTableB_of_residualsULCOUS8
    (hTE6 : GGTableBTwE6Round12Lang)
    (hE6 : GGE6ThreeRankSixTwoLocal) (hX6 : GGE6InnerDiagBoundThreeInput)
    (hO6 : GGE6OuterThreeInput) (hE7 : GGE7TwoRootAsInput) (hE8 : GGE8TwoRootAsInput)
    (hF4 : GGF4TwoRootAsInput) (hC : GGExcTwoCenterThreeInput)
    (hTX : GGTwE6InnerDiagBound2LInput) (hTR : GGTwE6RootAsInnInput)
    (hTR3 : GGTwE6RootAsInnThreeInput) (hTD3 : GGTwE6DeltaInput3)
    (hTC : GGTwE6CenterPrimeInput) (hTO : GGTwE6OuterPowInput)
    (hsR : GGStdSubSmallInputOn fun p lab =>
      ((((GGStdSubSmallRest5Label p lab ∧ ¬ GGLinTwoLabel p lab) ∧
        ¬ GGStdSubSmallOrthLabel p lab) ∧ ¬ (GGUnitDvd63Label p lab ∧ 2 ≤ lab.n)) ∧
          ¬ GGSpTwoThreeLabel p lab) ∧ ¬ GGUnitDvd63Label p lab)
    (hLie : GGLieLayerInput) :
    GGRemainderStdSubTableB :=
  ggRemainderStdSubTableB_of_residualsULCOUS5 hTE6
      (ggIOneOrthPlusFourInput_of_midClassCommute OPlusEight.midClassCommuteInput_holds)
      (ggStdSubIOneProperInputOn_exc_of_inputs hE6 hX6 hO6 hE7 hE8 hF4 hC hTX hTR hTR3 hTD3 hTC hTO)
      hsR hLie SmallOrth.plusTwoInput_holds SmallOrth.minusUnitInput_holds
      SmallOrth.twDFourInput_holds

end CFSG.Yardstones.M3f9567aba59d
