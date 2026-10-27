module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3LTFullSigmaFour
import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicThree
import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

theorem s21_14R3LT_dataOfSetup4 {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) :
    S21_14R3LT (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) :=
  s21_14R3LT_of_full_sigma
    CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
    CFSG.LocalAnalysis.RankThreeTheoremC.kFactOutCyclic_holds
    (fun _ hp => UC6.four_le_pRank_of_sigma hp)
    (s21_14R3LTFullSigma_dataOfSetup4 hS hU S hMS hPart)

end CFSG.LocalAnalysis.UniquenessCase.UC22
