module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.RankThreeCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOutPPrime
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Holds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.StrongThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72

variable {G : Type} [Group G] [Finite G]

section


theorem r72_dataOfSetup
    (hS : CFSG.LocalAnalysis.RankThreeUC.Standing G)
    (hUC : CFSG.Open.rankThreeUC G) (hC : CFSG.LocalAnalysis.RankThreeUC.AGL81TheoremC G)
    (S : CFSG.LocalAnalysis.RankThreeUC.Setup G) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F07.R72
      (CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three.dataOfSetup hS S) :=
  r72_dataOfSetup_of UCK.kFactSmallIdent_holds UCK.kFactOneLieIdent_holds
    UCK.stronglyEmbeddedCyclicOuter_holds
    (CFSG.AGLEmbedding.kFactSmallOutPPrime_of_smallIdent UCK.kFactSmallIdent_holds)
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group SEFive.stronglyEmbeddedFive_holds
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
    CFSG.AGLEmbedding.kFactReeInvolution hS hUC hC S

end

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72
