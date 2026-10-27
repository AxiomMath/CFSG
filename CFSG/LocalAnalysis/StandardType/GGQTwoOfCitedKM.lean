module

public import CFSG.LocalAnalysis.StandardType.GGQTwoOfCited
public import CFSG.LocalAnalysis.StandardType.GGWAutDefs
public import CFSG.LocalAnalysis.StandardType.GGWAutEngine
public import CFSG.LocalAnalysis.StandardType.GGWAutHeart
public import CFSG.LocalAnalysis.StandardType.GGWAutProp898

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggCorFiveTwentyInputQTwoOffE6Dep_of_citedKM
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h1 : GGQTwoModelInput)
    (h1b : GGQTwoNoTwoNodeIndInput)
    (h1x : GGQTwoXInLNbrModelInput)
    (h2 : GGQTwoLemma895Prime)
    (h3 : GGQTwoNoWeylA3)
    (h5 : GGQTwoCentralizerInput)
    (h8 : GGQTwoXInLDatum)
    (hGX : GGQ2GammaXGraphInput)
    (hPX : GGQ2GammaXPosE6Input)
    (hPN : GGQ2GammaNbrPosRestInput)
    (hPLD : GGQ2GammaNbrPosInLOn GGQ2SelD6)
    (hPLR : GGQ2GammaNbrPosInLOn GGQ2SelRest)
    (hnode : GGQ2TwoNodeInput)
    (hKM : GGReflClassOmegaInput)
    (hnm : GGQ2NoModelInput)
    (hF : GGQ2CavOfTBFull)
    (hH : GGQ2CavOfTBHeart)
    (hT : GGQ2TableBI1Fail)
    (hΓ : GGQ2GammaXOffI1Input)
    (hNO : GGQ2Prop898NotOrth)
    (hP3 : GGQ2P3OffI1Input)
    (hE : GGQ2ReflEInput)
    (hK : GGQ2ReflKInput)
    (hR : GGQ2ReflRestOutInput) :
    GGCorFiveTwentyInputQTwoOffE6Dep :=
  ggCorFiveTwentyInputQTwoOffE6Dep_of_cited hLB hP h1 h1b h1x h2 h3 h5 h8 hGX hPX hPN hPLD hPLR
    hnode (ggWAut_heartE6 (ggWAut_engine hKM) hKM) hnm hF hH hT hΓ
    (ggQ2Prop898_of_engine (ggWAut_engine hKM) hNO) hP3 hE hK hR

end CFSG.StandardType

end
