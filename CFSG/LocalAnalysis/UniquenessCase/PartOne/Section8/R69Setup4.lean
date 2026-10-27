module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneSixNine
public import CFSG.LocalAnalysis.UniquenessCase.UC6Star36b
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporGe4
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36ODCCent
public import CFSG.LocalAnalysis.UniquenessCase.UC6K316Out
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporPairs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt)

variable {G : Type} [Group G] [Finite G]

theorem r6_9_dataOfSetup4_of_K36 (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G)
    (S : Setup4 G) (hMS : S.InMSigma) (hC : TheoremCAt S.M) (hK : UCK.K36) :
    R6_9 (dataOfSetup4 hS hU S) :=
  PartTwo.r6_9_of_r6_7 _ (r6_3_dataOfSetup4 hS hU S hC)
    (PartTwo.r6_7_of_K36_at _ hK (r6_3_dataOfSetup4 hS hU S hC)
      (star36At_dataOfSetup4 hS hU S hMS hC))

theorem r6_9_dataOfSetup4
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hC : TheoremCAt S.M) :
    R6_9 (dataOfSetup4 hS hU S) :=
  r6_9_dataOfSetup4_of_K36 hS hU S hMS hC (UCK.k36_of_eqlStar
      (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
          UCK.k36OddDefChar_holds UCK.k315Spor_holds UCK.k36EqlStarSporGe4_holds) UCK.l34OuterFree)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
