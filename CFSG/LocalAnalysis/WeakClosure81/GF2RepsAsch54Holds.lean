module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Open
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverRankFive
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TripleCoverWide
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch22Main
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.NoncyclicCentre
import CFSG.HardMathSupport.Timmesfeld.Coordinator.ScopeBFrontier
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogSchreier
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BlockLiftQ
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.EngineOver

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem asch5_4_holds : Asch5_4 :=
  asch5_4_of_open CFSG.AGLEmbedding.kFactCatalogSchreier_holds
    (asch2_2Simple_of_kfacts
        (CFSG.AGLEmbedding.kFactCoverRankFive_of
            CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
            CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
        (RankThreeTheoremC.KFactProofs.T29.noncyclicCentreRank_of_tables
            CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
            (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
                CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds))
        (RankThreeTheoremC.KFactProofs.Stroth.TripleCover.kFactAlphaListM3Wide_of_tables
            CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
            CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
        CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv)

end CFSG.LocalAnalysis.WeakClosure81

end
