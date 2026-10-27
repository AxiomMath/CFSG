module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAssemble
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXHolds
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaNbrHolds
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXInL
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaNbrInL
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaNbrDet
public import CFSG.LocalAnalysis.StandardType.GGQTwoGraphK
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXPosLeaf
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaNbrPosE6
public import CFSG.LocalAnalysis.StandardType.GGQTwoPosInLE6
public import CFSG.LocalAnalysis.StandardType.GGQTwoDepLin
public import CFSG.LocalAnalysis.StandardType.GGQTwoI1FailGlue

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggCorFiveTwentyInputQTwoOffE6Dep_of_cited
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
    (hHeart : GGQ2HeartInput)
    (hnm : GGQ2NoModelInput)
    (hF : GGQ2CavOfTBFull)
    (hH : GGQ2CavOfTBHeart)
    (hT : GGQ2TableBI1Fail)
    (hΓ : GGQ2GammaXOffI1Input)
    (h898 : GGQ2Prop898)
    (hP3 : GGQ2P3OffI1Input)
    (hE : GGQ2ReflEInput)
    (hK : GGQ2ReflKInput)
    (hR : GGQ2ReflRestOutInput) :
    GGCorFiveTwentyInputQTwoOffE6Dep := by
  have hgx : GGQ2GammaXInput :=
    ggQ2_gammaX_holds hLB hP h1 h1b h5 hnode hGX (ggQ2_gammaXPos_of_e6 hLB hP h5 hPX)
  have hgn : GGQ2GammaNbrInput :=
    ggQ2_gammaNbr_holds hLB hP h1 h1b h5 hnode (ggQ2_gammaNbrGraph_holds hLB hP h1b h5 hnode)
      (ggQ2_gammaNbrDet_holds hLB hP h5)
      (ggQ2_gammaNbrPos_of_rest_cell hPN (ggQ2_gammaNbrPosE6Cell_holds hHeart hLB hP h5)
        (ggQ2_posNbr_innerCell hLB hP h5))
  have hgxL : GGQ2GammaXInLInput :=
    ggQ2_gammaXInL_holds ggLNoncyclicInput_holds hLB hP h1 h1b h1x h5 h8 hnode
  have hgnL : GGQ2GammaNbrInLInput :=
    ggQ2_gammaNbrInL_holds hLB hP h1b h5 hnode
      (ggQ2_gammaNbrDetAt_holds hLB hP h5 GGQ2PosInL)
      (ggQ2_posInL_of_cells hPLR hPLD (ggQ2_posInL_lineE6 hLB hP h5))
  have hi1 : GGQ2I1FailInput :=
    ggQ2_i1FailInput_of_pieces hLB hP hF hH hT hΓ h898 hP3 hE hK hR
  exact ggCorFiveTwentyInputQTwoOffE6Dep_of_layers hLB hP h1 h1b h2 h3 h5 hgx hgn hgxL hgnL
    hnode (ggQ2_dependentOther_of_heart hHeart) hi1 hnm

end CFSG.StandardType

end
