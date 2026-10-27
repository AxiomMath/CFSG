module

public import CFSG.LocalAnalysis.StandardType.GGQTwoOfCitedKM
public import CFSG.LocalAnalysis.StandardType.GGQTwoNoModelEngine
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXPosE6
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXInnerBCCell
public import CFSG.LocalAnalysis.StandardType.GGQTwoP3Heart
public import CFSG.LocalAnalysis.StandardType.GGQTwoDepHeart
public import CFSG.LocalAnalysis.StandardType.GGQ2NotOrthGlue
public import CFSG.LocalAnalysis.StandardType.GGWeylE7NoEichler

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggCorFiveTwentyInputQTwoOffE6Dep_of_citedKM4
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h1 : GGQTwoModelInput)
    (h1b : GGQTwoNoTwoNodeIndInput)
    (h1x : GGQTwoXInLNbrModelInput)
    (h2 : GGQTwoLemma895Prime)
    (h3 : GGQTwoNoWeylA3)
    (h5 : GGQTwoCentralizerInput)
    (h8 : GGQTwoXInLDatum)
    (hGX : GGQ2GammaXGraphInput)
    (hPX : GGQ2GammaXPosNoModelInput)
    (hPN : GGQ2GammaNbrPosRestInput)
    (hPLD : GGQ2GammaNbrPosInLOn GGQ2SelD6)
    (hPLR : GGQ2GammaNbrPosInLOn GGQ2SelRest)
    (hnode : GGQ2TwoNodeInput)
    (hKM : GGReflClassOmegaInput)
    (hnm : GGQ2NoModelRest2Input)
    (hF : GGQ2CavOfTBFull)
    (hH : GGQ2CavOfTBHeart)
    (hT : GGQ2TableBI1Fail)
    (hΓ : GGQ2GammaXOffI1Input)
    (hI : GGQ2HeartBI1)
    (hP3 : GGQ2P3OffI1RestInput)
    (hE : GGQ2ReflEInput)
    (hK : GGQ2ReflKInput)
    (hR : GGQ2ReflRestOutInput) :
    GGCorFiveTwentyInputQTwoOffE6Dep :=
  ggCorFiveTwentyInputQTwoOffE6Dep_of_citedKM hLB hP h1 h1b h1x h2 h3 h5 h8 hGX
    (ggQ2_gammaXPosE6_of_noModel (ggQ2_heartInput_of_omega hKM) hLB hP h5 hPX) hPN hPLD
    hPLR hnode hKM (ggQ2_noModel_of_rest2_cell hnm (ggQ2_noModel_engineCell (ggWAut_engine hKM)))
    hF hH hT hΓ
    (ggQ2Prop898NotOrth_of_pieces hLB hP hF hH hT hI ggWeylE7NoEichler_holds)
    (ggQ2_p3_of_rest_cell hP3 ggQ2_p3_heartCell) hE hK hR

end CFSG.StandardType

end
