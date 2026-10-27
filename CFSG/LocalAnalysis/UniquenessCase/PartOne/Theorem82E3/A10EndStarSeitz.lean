module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndTwoGen
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndStarExcBal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.HardMathSupport.Solomon.Coordinator

theorem kFactE27SignalizerLayer_of_kFacts
    (hK : Theorem82.K34odd)
    (hB : CFSG.HardMathSupport.Dickson.Bal207.Bal207Corr)
    (h717 : RankThreeUC.AGL81C.SevenOneSeven)
    (hO3 : RankThreeTheoremC.KFactOutThreePrimeSimple) (hA3 : KFactAutThreeRankTwo)
    (hSF : SignalizerFunctorTheoremK)
    (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge) : KFactE27SignalizerLayer :=
  kFactE27SignalizerLayer_of_comp <| kFactE27SignalizerComp_of_one <|
    kFactE27SignalizerOne_of_almostSimple <| kFactE27SignalizerAlmostSimple_of_sylow h717 hO3 hA3 <|
      kFactE27SignalizerAlmostSimpleSylow_of_twoGen hSF hbridge (kFactE27TwoGen_of_k34odd hK)
        (kFactE27SignalizerExceptional_of_bal hB)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
