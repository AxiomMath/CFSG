module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoRoot
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoDelta
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoNormSmall
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoDeltaSmall
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvd63
public import CFSG.LocalAnalysis.StandardType.GGRemStdSubResidualsULCOU
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveMain
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFinHigh
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveSpRoot
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveU52Assembly
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFourMain
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveUDvdRRoot
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveUDeltaNode
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthInPlus
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthInMinus

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly CFSG.StandardType

theorem unitDvd63Q2Input_holds :
    UnitDvd63Q2Input :=
  fun _ _ _ hK => ⟨ggStdSubTwoTorusNormSmallR_sixTwo hK, ggStdSubTwoTorusDeltaSmall_sixTwo hK⟩

end CFSG.StandardType.USixTwo

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.USixTwo

theorem ggRemainderStdSubTableB_of_residualsULCOUS5
    (hTE6 : GGTableBTwE6Round12Lang)
    (hP : GGIOneOrthPlusFourInput) (hX : GGStdSubIOneProperInputOn GGIOneRestFiveExcLabel)
    (hsR : GGStdSubSmallInputOn fun p lab =>
      ((((GGStdSubSmallRest5Label p lab ∧ ¬ GGLinTwoLabel p lab) ∧
        ¬ GGStdSubSmallOrthLabel p lab) ∧ ¬ (GGUnitDvd63Label p lab ∧ 2 ≤ lab.n)) ∧
          ¬ GGSpTwoThreeLabel p lab) ∧ ¬ GGUnitDvd63Label p lab)
    (hLie : GGLieLayerInput) (h2 : SmallOrth.PlusTwoInput) (h4 : SmallOrth.MinusUnitInput)
    (h5 : SmallOrth.TwDFourInput) :
    GGRemainderStdSubTableB :=
  ggRemainderStdSubTableB_of_residualsULCOU hTE6
      (ggStdSubIOneProperInputOn_restFive_of_exc ggLNoncyclicInput_holds
          (IOneUDvdR.ggIOneUnitaryDvdRootInput_of_sixTwo ggIOneUnitaryDvdRootSixTwo_holds)
          (IOneUDelta.ggIOneUnitaryDvdDeltaInput_of_sixTwo ggIOneUnitaryDvdDeltaSixTwo_holds)
          ggIOneUnitaryFiveTwoInput_holds ggIOneSpTwoRootInput_holds hP hX)
      (ggStdSubSmallInputOn_of_not_spTwo' ggSpTwoNormSmallRFour_holds ggSpTwoNormSmallRHigh_holds
          (ggStdSubSmallInputOn_of_not_unitDvd63 unitDvd63Q2Input_holds hsR)) hLie
      SmallOrth.plusSplitInput_holds h2 SmallOrth.minusSplitInput_holds h4 h5

end CFSG.Yardstones.M3f9567aba59d

end
