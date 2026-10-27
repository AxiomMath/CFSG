module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Q35
public import CFSG.LocalAnalysis.UniquenessCase.UC22S211Setup4
import CFSG.LocalAnalysis.UniquenessCase.UC22R82Four
import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C5Res
import CFSG.LocalAnalysis.UniquenessCase.UC22S215Setup4
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3BadNoStrongHolds
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBA6
import CFSG.LocalAnalysis.UniquenessCase.UC22FieldAutOddHolds
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporGe4
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36ODCCent
public import CFSG.LocalAnalysis.UniquenessCase.UC6K316Out
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporPairs
import CFSG.LocalAnalysis.UniquenessCase.UC6R77Three
import CFSG.LocalAnalysis.UniquenessCase.UC22Sec7Three


public import CFSG.LocalAnalysis.UniquenessCase.UC22S214U
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableOf
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229KThin

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig

import CFSG.LocalAnalysis.UniquenessCase.UC6S846h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedSolvableQ StronglyEmbeddedThree BadNoStrongThree)


theorem s21_12aFR34F3Q35_dataOfSetup4 {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) :
    S21_12aFR34F3Q35 (UC6.dataOfSetup4 hS hU S) (Choice214U (UC6.dataOfSetup4 hS hU S)) := by
  have hSE : StronglyEmbeddedFive := PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
  have hB3 : BadNoStrongThree := PartOne.Section7.badNoStrongThree_holds
  have hG3 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
  have hK3 : StronglyEmbeddedThree :=
    PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3 CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
  have hSQ : StronglyEmbeddedSolvableQ :=
    PartOne.Section7.stronglyEmbeddedSolvableQ_of_kFacts UCK.kFactSmallIdent_holds
      UCK.kFactOneLieTorus_holds UCK.stronglyEmbeddedCyclicOuter_holds
      CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4
  have hKF7 := kf7Use_dataOfSetup4 hSQ hSE hK3 hB3 hS hU S hMS
  obtain ⟨h207, h211⟩ := s20_7_s21_1_dataOfSetup4 hS hU S hMS hPart
    (Choice214U (UC6.dataOfSetup4 hS hU S))
  have hK36 := UCK.k36_of_eqlStar
      (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
          UCK.k36OddDefChar_holds UCK.k315Spor_holds UCK.k36EqlStarSporGe4_holds) UCK.l34OuterFree
  have hC76 := PartOne.Section7.c76Three_of_inputs hSE hK3 hB3 hS hU S
  have hUse := UC6.r77Use_dataOfSetup4_of_K36_of_C76Three hSE hK36 hS hU S hMS hPart.1 hC76
  have h614 := (UC6.r6_14_dataOfSetup4_iff hS hU S).2 hPart.2.1
  have h76 : F07.R76Sig (UC6.dataOfSetup4 hS hU S) := fun p hp _ hsp => by
    by_cases h3 : 3 ∈ uniqueFourBeta G
    · exact hC76 hMS h3 p hp hsp
    · exact UC6.conclusion76_dataOfSetup4 hSE hS hU S h3 hp hsp
  have h82 := r82_dataOfSetup4 hS hU S hPart.2.2
  have h5 : S21_5 (UC6.dataOfSetup4 hS hU S) (Choice214U (UC6.dataOfSetup4 hS hU S)) :=
    s21_5_setup4 hSQ hSE hK3 hB3 KBridge.kThinSimple_holds hS hU S hMS h82
      (s21_15Two_four_certificate113 _ _ h211 (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
        (by have := hS.rank; omega) (fun _ _ hp => UC6.four_le_pRank_of_sigma hp) hUse.1 h614
        (fun p hp hsp => h76 p hp ((UC6.dataOfSetup4 hS hU S).sig_prime p hp).2 hsp))
  exact s21_12aFR34F3Q35_of_kFacts CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
    (UC6S846.sigmaStd_dataOfSetup4 hS hU S) hKF7 h5 h207
    kFieldAutOdd_holds kFunCount_holds kFunSplit_holds kQ35PermFunCent_holds

end CFSG.LocalAnalysis.UniquenessCase.UC22
