module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.UniquenessCase.UC22DichotomyHolds
import CFSG.RankThree.PartOne.TCB.SchreierFinal
import CFSG.RankThree.SubgroupLists.MitchellPartThreeProof
import CFSG.LocalAnalysis.UniquenessCase.UC22ListB
import CFSG.LocalAnalysis.UniquenessCase.UC22K318Main
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.LocalAnalysis.UniquenessCase.UC22P20e
import CFSG.LocalAnalysis.UniquenessCase.UC22P20h
import CFSG.LocalAnalysis.UniquenessCase.UC6S6
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltThreeRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwo
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ScalarTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Survivor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ThreeStrong
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm47Statement
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoJ3
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoONan
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.LocalAnalysis.UniquenessCase.UC6R2
public import CFSG.RankThree.PartOne.Mult.Sec68
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.OrderCheckF
public import CFSG.Sporadic.Fi24
public import CFSG.Sporadic.Recognition.LyonsAmalgamModelYAut
public import CFSG.Sporadic.Recognition.LyonsFinalDist2
public import CFSG.Sporadic.Suz
import CFSG.LocalAnalysis.UniquenessCase.UC6S9
import CFSG.RankThree.PartOne.SPOR.OuterSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt)

variable {G : Type} [Group G] [Finite G]


theorem s20_5_dataOfSetup4 (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hC : TheoremCAt S.M) : S20_5 (UC6.dataOfSetup4 hS hU S) := by
  have h124 := s20_1_124 _ (UC6.r6_6_dataOfSetup4 hS hU S hMS hC) listBNonabelian
  have h202 := s20_2_of _ (K318.k318_of_mitchell
    CFSG.RankThree.SubgroupLists.mitchellPartThree_holds) h124
  exact s20_5_of _ h202 (s20_3_of _ h124 h202 listBNonabelian
    CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds quasisimpleDichotomy_holds
    (uc22p20h_five _ threeNoncentralFact_holds)) listBNonabelian listBNotSmall

end CFSG.LocalAnalysis.UniquenessCase.UC22
