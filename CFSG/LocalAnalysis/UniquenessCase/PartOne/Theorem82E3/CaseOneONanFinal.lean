module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ3c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

theorem onanExcludedSetup_of_finiteFacts :
    ONanExcludedSetup :=
  onanExcludedSetup_of_inputs
      (Section7.stronglyEmbeddedSolvableQ_of_kFacts UCK.kFactSmallIdent_holds
          UCK.kFactOneLieTorus_holds UCK.stronglyEmbeddedCyclicOuter_holds
          CFSG.AGLEmbedding.kFactCatalogSchreier_holds
          CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4)
      Section7.SEFive.stronglyEmbeddedFive_holds
      (Section7.StronglyEmbeddedThree_of_KIB
          RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
          CFSG.AGLEmbedding.kFactCatalogSchreier_holds
          (Section7.StronglyEmbeddedThreeKIB_of_small
              RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
              Section7.KIB3Small_holds)) ONan.onanCentralizerSetup_of_finiteFacts

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
