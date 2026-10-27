module

public import CFSG.LocalAnalysis.StandardType.GGIOneExcAssembly
public import CFSG.LocalAnalysis.StandardType.GGLieLayerRecipe
public import CFSG.LocalAnalysis.StandardType.GGIOneExcFacts
public import CFSG.LocalAnalysis.StandardType.GGIOneExcOuterE6
public import CFSG.LocalAnalysis.StandardType.GGIOneExcOuterTwE6
public import CFSG.LocalAnalysis.StandardType.GGIOneExcCenterTwE6

public section

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG CFSG.Assembly CFSG.StandardType


theorem ggRemainderStdSubTableB_of_residualsULCOUS9
    (hTE6 : GGTableBTwE6Round12Lang) (hX6 : GGE6InnerDiagBoundThreeInput)
    (hE7 : GGE7TwoRootAsInput) (hE8 : GGE8TwoRootAsInput) (hF4 : GGF4TwoRootAsInput)
    (hTX : GGTwE6InnerDiagBound2LInput) (hTR : GGTwE6RootAsInnInput)
    (hTR3 : GGTwE6RootAsInnThreeInput) (hTD3 : GGTwE6DeltaInput3)
    (hsR : GGStdSubSmallInputOn fun p lab =>
      ((((GGStdSubSmallRest5Label p lab ∧ ¬ GGLinTwoLabel p lab) ∧
        ¬ GGStdSubSmallOrthLabel p lab) ∧ ¬ (GGUnitDvd63Label p lab ∧ 2 ≤ lab.n)) ∧
          ¬ GGSpTwoThreeLabel p lab) ∧ ¬ GGUnitDvd63Label p lab) :
    GGRemainderStdSubTableB :=
  ggRemainderStdSubTableB_of_residualsULCOUS8 hTE6 ggE6ThreeRankSixTwoLocal_holds hX6
    ggE6OuterThreeInput_holds hE7 hE8 hF4 ggExcTwoCenterThreeInput_holds hTX hTR hTR3 hTD3
    ggTwE6CenterPrimeInput_holds ggTwE6OuterPowInput_holds hsR LieLayer.ggLieLayerInput_holds

end CFSG.Yardstones.M3f9567aba59d

end
