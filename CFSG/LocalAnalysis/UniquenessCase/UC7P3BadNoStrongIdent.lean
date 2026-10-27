module

public import CFSG.LocalAnalysis.UniquenessCase.UC7P3BadNoStrong
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsIdent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.AGLEmbedding
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)

theorem badIdentification_of_kfacts (hId : KFactSmallIdent) (hLie : KFactOneLieIdent)
    (hCyc : CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact) :
    BadIdentification :=
  fun _ hp hp5 _ _ _ hX hO h2 _ hN =>
    identification_of_isStronglyPEmbedded hId hLie hCyc hp hp5 hX hO h2 hN

theorem badNoStrongThree_of_identification (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hUO : KFactUnitaryOrder) (hRO : KFactReeOrder) (hOrd : BadListOrders)
    (hId : KFactSmallIdent) (hLie : KFactOneLieIdent)
    (hCyc : CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact) :
    BadNoStrongThree :=
  badNoStrongThree_of_kfacts hG3 hUO hRO hOrd (badIdentification_of_kfacts hId hLie hCyc)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
