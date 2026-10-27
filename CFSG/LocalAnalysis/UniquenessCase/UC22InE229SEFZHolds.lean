module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229SEFZH
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35Holds
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.J4Eleven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

section Certificates


theorem stronglyEmbeddedFiveZ_holds
    : StronglyEmbeddedFiveZ :=
  stronglyEmbeddedFiveZ_of_kFacts UCK.kFactSmallIdent_holds UCK.kFactOneLieIdent_holds
    UCK.stronglyEmbeddedCyclicOuter_holds CFSG.AGLEmbeddingD2.d2HeisLocalAt_mcl
    CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
