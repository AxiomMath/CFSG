module

public import CFSG.LocalAnalysis.UniquenessCase.UC7P3BadNoStrongIdent
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3BadOrders
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35Holds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.StrongThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.AGLEmbedding

section Holds


theorem badNoStrongThree_holds
    : BadNoStrongThree :=
  badNoStrongThree_of_identification
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
    kFactUnitaryOrder kFactReeOrder badListOrders_holds UCK.kFactSmallIdent_holds
    UCK.kFactOneLieIdent_holds UCK.stronglyEmbeddedCyclicOuter_holds

end Holds

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
