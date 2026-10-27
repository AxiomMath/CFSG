module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Holds
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332K33
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3BadNoStrongHolds
import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive
import CFSG.LocalAnalysis.AGLEmbedding.CatalogSchreier
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableOf
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7
import CFSG.LocalAnalysis.UniquenessCase.UC1K462Holds
import CFSG.LocalAnalysis.UniquenessCase.UC1ZassMain
import CFSG.LocalAnalysis.UniquenessCase.UC6K332RowsHolds
import CFSG.LocalAnalysis.UniquenessCase.UCK461Holds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddFrob
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddGt7
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddSetup4
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBA6
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R92b
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedSolvableQ StronglyEmbeddedThree BadNoStrongThree)

variable {G : Type} [Group G] [Finite G]


theorem r920odd_dataOfSetup4
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) :
    PartOne.Section9.R920odd (UC6.dataOfSetup4 hS hU S) := by
  have hSE : StronglyEmbeddedFive := PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
  have hB3 : BadNoStrongThree := PartOne.Section7.badNoStrongThree_holds
  have hG3 := RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
  have hK3 : StronglyEmbeddedThree :=
    PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3 CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
  have hSQ : StronglyEmbeddedSolvableQ :=
    PartOne.Section7.stronglyEmbeddedSolvableQ_of_kFacts UCK.kFactSmallIdent_holds
      UCK.kFactOneLieTorus_holds UCK.stronglyEmbeddedCyclicOuter_holds
      CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4
  have hK332 : UCK.K332Cyc :=
    UCK.K332Route.k332Cyc_of_rows UCK.K332Route.k33_holds UCK.K332Route.k332Rows_holds
  have hZ : UCK.ZassenhausPerfect := UCK.Zass.zassenhausPerfect_holds
  exact PartOne.Section9.r920odd_dataOfSetup4_of_branches hSE hK3 hB3 hSQ hK332 hS hU S hMS hPart
    (fun L D₃ Y H q Sl hq E hE hN => Sl.false_of_hN_gt_seven hq hN hE UCK.k32_holds
      UCK.k461_holds UCK.k462_holds CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      CFSG.CGT.PushingUpLit.CGT6.sporadicThreeCenterSmallPrimes_holds
      CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement hZ)
    fun L D₃ Y H q Sl hq E hE hN => by
      have h92 := F09.r92_of_inputs UCK.k32_holds CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        (UC6.dataOfSetup4 hS hU S) Y H E hE Sl.H_ne_top
      exact Sl.false_of_hN_eq_seven hq hN hE h92.1 h92.2
        (Sl.I9_le_M_of_odd_dvd hN hE ⟨3, Nat.prime_three, by norm_num, by rw [hq]; norm_num⟩
          UCK.k461_holds UCK.k462_holds CFSG.AGLEmbedding.kFactCatalogSchreier_holds)

end CFSG.LocalAnalysis.UniquenessCase.UC22
