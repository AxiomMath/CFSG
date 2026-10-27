module

public import CFSG.LocalAnalysis.StandardType.GGQTwoOfCitedKM4
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXPosAmb
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXOffI1Holds
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXGraphHolds
public import CFSG.LocalAnalysis.StandardType.GGQTwoTBCGraphF4
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
import CFSG.LocalAnalysis.StandardType.GGQ2S08RestOut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggCorFiveTwentyInputQTwoOffE6Dep_of_citedKM4C
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h1 : GGQTwoModelInput)
    (h1b : GGQTwoNoTwoNodeIndInput)
    (h1x : GGQTwoXInLNbrModelInput)
    (h2 : GGQTwoLemma895Prime)
    (h3 : GGQTwoNoWeylA3)
    (h5 : GGQTwoCentralizerInput)
    (h8 : GGQTwoXInLDatum)
    (hGX : GGQ2GammaXGraphInput)
    (hamb : GGQ2AmbModelInput)
    (hga : GGQ2GammaXGraphD5AmbInput)
    (hPN : GGQ2GammaNbrPosRestInput)
    (hPLD : GGQ2GammaNbrPosInLOn GGQ2SelD6)
    (hPLR : GGQ2GammaNbrPosInLOn GGQ2SelRest)
    (hnode : GGQ2TwoNodeInput)
    (hKM : GGReflClassOmegaInput)
    (hnm : GGQ2NoModelRest2Input)
    (hF : GGQ2CavOfTBFull)
    (hH : GGQ2CavOfTBHeart)
    (hT : GGQ2TableBI1Fail)
    (hI : GGQ2HeartBI1)
    (hP3 : GGQ2P3OffI1RestInput)
    (hE : GGQ2ReflEInput)
    (hK : GGQ2ReflKInput) :
    GGCorFiveTwentyInputQTwoOffE6Dep :=
  have hΓ : GGQ2GammaXOffI1Input := ggQ2_gammaXOffI1_holds hLB hP hT hI
    (ggQ2_gammaXOffI1Graph_of_tbc hLB hP ggQ2TBCGraphInput_holds)
  ggCorFiveTwentyInputQTwoOffE6Dep_of_citedKM4 hLB hP h1 h1b h1x h2 h3 h5 h8 hGX
    (ggQ2_gammaXPosNoModel_of_ambRes ggLNoncyclicInput_holds hLB hP h1 h1b h5 hamb hga)
    hPN hPLD hPLR hnode hKM hnm hF hH hT hΓ hI hP3 hE hK
    (ggQ2s08_reflRestOut_holds hLB hP hΓ)

end CFSG.StandardType
