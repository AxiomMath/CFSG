module

public import CFSG.RankThree.PartTwo.Sec21.LitScopeProofGL83Strong
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.FrontierSeitz
public import CFSG.LieType.SeitzGeneration.ConsumerEx
public import CFSG.HardMathSupport.Malle.SeitzCube.InnerExFrontier
public import CFSG.LieType.SeitzGeneration.ExcSeitzStatus
import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Main
import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.RankOneA1Case
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusU3
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusReeG2
import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.F4Phi3
import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.E8Phi5
import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Final
import CFSG.LieType.SeitzGeneration.SpF2.Main
import CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.SUOddTwoBig
import CFSG.LieType.SeitzGeneration.OmegaF2.Plus
import CFSG.LieType.SeitzGeneration.OmegaF2.Minus
public import CFSG.LieType.SeitzGeneration.RootPairOrthMinusChar2
public import CFSG.LieType.SeitzGeneration.RootPairOrthPlusChar2

public section

namespace CFSG.RankThree.PartTwo.Sec21.RonanYS15

open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

theorem gl83StronglyEmbeddedNoSimpleThree_holds :
    CFSG.RankThree.PartTwo.Sec21.GL83StronglyEmbeddedNoSimpleThree := by
  have hAniN :
      CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.SeitzExcAnisotropicNotG2ThreePlus :=
    CFSG.LieType.SeitzGeneration.seitzExcAnisotropicNotG2ThreePlus_of_yardsticks
      ⟨CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.seitzExcAnisotropicF4Class_three,
        CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.seitzExcAnisotropicF4Class_six⟩
      ⟨CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.seitzExcAnisotropicE6Class_six,
        CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.seitzExcAnisotropicE8Class_five,
        CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.seitzExcAnisotropicE8Class_ten,
        CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.seitzExcAnisotropicE8Class_twelve⟩
      (CFSG.HardMathSupport.Seitz.TrialityEven.seitzExcAnisotropicTrialityEvenThree_of_leaves
        CFSG.HardMathSupport.Seitz.TrialityEven.trialityTwoThreePlanes_holds)
  have hOut : CFSG.LieType.SeitzGeneration.SeitzOuterLowN :=
    (CFSG.HardMathSupport.Malle.SeitzCube.innerEx_lowN_of_pairs_aniso
      CFSG.LieType.SeitzGeneration.subfieldPairSpF2_holds
      CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.subfieldPairSUOddTwo_holds
      (CFSG.LieType.SeitzGeneration.subfieldPairOmegaPlusChar2_of_F2
        CFSG.LieType.SeitzGeneration.subfieldPairOmegaPlusF2_holds)
      (CFSG.LieType.SeitzGeneration.subfieldPairOmegaMinusChar2_of_F2
        CFSG.LieType.SeitzGeneration.subfieldPairOmegaMinusF2_holds)
      hAniN CFSG.LieType.SeitzGeneration.seitzExcOuterNarrow_holds).2.2
  have hR1 : ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 3 →
      CFSG.AGLEmbedding.IsRankOneLieIndex d.1 → Gls3PlusCase (.lie d) := by
    intro d h3 hd
    rcases hd with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨m, hm⟩
    · exact gls3PlusCase_lie_rankOne_A1 q (by simpa [hq] using h3) d hq
    · exact gls3PlusCase_lie_rankOne_U3 q (by simpa [hq] using h3) d hq
    · exact gls3PlusCase_lie_reeG2 m d hm
  exact gl83StronglyEmbeddedNoSimpleThree_of_kFactStrongThreeSolv
    (kFactStrongThreeSolv_of_gls3 CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
        (gls3_of_plus
            (gls3StronglyThreeEmbeddedPlus_of_seitz
                (CFSG.LieType.SeitzGeneration.offCharGen_of_seitzEx
                    (CFSG.HardMathSupport.Malle.SeitzCube.kFactSeitzRankTwoInnerEx_of_anisoN hAniN))
                hOut hR1)))

end CFSG.RankThree.PartTwo.Sec21.RonanYS15
