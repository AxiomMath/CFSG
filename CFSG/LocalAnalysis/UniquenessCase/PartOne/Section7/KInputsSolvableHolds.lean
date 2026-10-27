module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableOf
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35Holds
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogSchreier
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.J4Eleven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

theorem stronglyEmbeddedSolvable_holds :
    StronglyEmbeddedSolvable :=
  stronglyEmbeddedSolvable_of_kFacts
    CFSG.LocalAnalysis.UniquenessCase.UCK.kFactSmallIdent_holds
    CFSG.LocalAnalysis.UniquenessCase.UCK.kFactOneLieTorus_holds
    CFSG.LocalAnalysis.UniquenessCase.UCK.stronglyEmbeddedCyclicOuter_holds
    CFSG.AGLEmbedding.kFactCatalogSchreier_holds
    CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
