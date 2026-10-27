module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Holds
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporGe4
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36ODCCent
public import CFSG.LocalAnalysis.UniquenessCase.UC6K316Out
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporPairs
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3BadNoStrongHolds
import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229SEFZHolds
import CFSG.LocalAnalysis.UniquenessCase.UC22P22th
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229L34Res
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229U3Three
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z3Three
import CFSG.LocalAnalysis.UniquenessCase.UC22Sec7Three
import CFSG.LocalAnalysis.UniquenessCase.UC6R77Three
import CFSG.LocalAnalysis.UniquenessCase.UC6S846j
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBA6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedThree BadNoStrongThree)

variable {G : Type} [Group G] [Finite G]


theorem r847_dataOfSetup4
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) : F08.R847 (UC6.dataOfSetup4 hS hU S) := by
  have hSE : StronglyEmbeddedFive := PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
  have hB3 : BadNoStrongThree := PartOne.Section7.badNoStrongThree_holds
  have hG3 := RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
  have hK3 : StronglyEmbeddedThree :=
    PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3 CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
  have hgr := CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
  have hC76 := PartOne.Section7.c76Three_of_inputs hSE hK3 hB3 hS hU S
  have hUse := UC6.r77Use_dataOfSetup4_of_K36_of_C76Three hSE (UCK.k36_of_eqlStar
      (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
          UCK.k36OddDefChar_holds UCK.k315Spor_holds UCK.k36EqlStarSporGe4_holds) UCK.l34OuterFree)
    hS hU S hMS hPart.1 hC76
  have h846 := UC6S846.r846_dataOfSetup4 hgr hS hU S hPart hUse.1
  exact r847_of_r847E4
    (r847E4_setup4_of_resQ hSE PartOne.Section7.stronglyEmbeddedFiveZ_holds hB3
      PartTwo.thinList13_holds RankThreeTheoremC.kFactOutCyclic_holds hS hU S hMS hgr
      uc22pwCartanSU3_holds h846 (r847U3Three_setup4 hSE hgr hS hU S hMS)
      (r847ResQ_of_three hG3 CFSG.AGLEmbedding.kFactReeInvolution hK3 PartTwo.thinList13_holds
        RankThreeTheoremC.kFactOutCyclic_holds hS hU S hgr uc22pwCartanSU3_holds
        (l34GFResidueAt_of_torus uc22pwTorusSU3_holds hgr hS hU S h846)))

end CFSG.LocalAnalysis.UniquenessCase.UC22
