module

public import CFSG.RankThree.PartTwo.Sec4.Census.Ronan41List42
public import CFSG.RankThree.PartOne.N143.SectionListFinal
public import CFSG.RankThree.PartOne.N143.O7
public import CFSG.RankThree.PartOne.SRC.Closed
public import CFSG.RankThree.PartOne.SLB4A.Final
public import CFSG.RankThree.PartOne.SLB4B.Assemble
public import CFSG.RankThree.PartOne.CTP.StrongPThree
public import CFSG.RankThree.PartOne.CTP.SpinRankFour
public import CFSG.RankThree.PartOne.CTP.BabyRankFour
public import CFSG.RankThree.PartOne.MultRes.Sec68Closed
public import CFSG.RankThree.PartOne.S11c.ETypeRankThree
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive
public import CFSG.RankThree.PartOne.N143.T2LargeAll
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringInputs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne.Census3
open CFSG.Assembly.RankThreeEven (localRank)

section List

theorem list42_of_simple_section {L : Type} [Group L] [Finite L] (hL : SectionFourHyp L)
    (H : Subgroup L) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) (π : H →* S) (hπ : Function.Surjective π) :
    List42 S := by
  obtain ⟨hq, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab
  have hSLB : PartOne.N143.SectionListBound :=
    PartOne.N143.sectionListBound_of_four_leaves
        (PartOne.MultRes.sec6Eight_of_griess
            CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement)
        PartOne.TCB.tauCetiCatalogBridge (PartOne.CTP.threeCatalog_of_spin PartOne.CTP.spinRankFour
            PartOne.CTP.rankFourBabyMonster)
        CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
        PartOne.actualCoverETypeRankThreeOnlyE6FieldTwo CFSG.TauCetiBridge.Even.chevalleyBridgesAll
        PartOne.N143.noOddCentralCoverFor_o7 PartOne.SRC.noHardLowTwo
        (PartOne.SLB4A.twoPowFiveFor_isLieTwoPowFiveIndex
            CFSG.TauCetiBridge.Even.chevalleyBridgesAll)
        PartOne.SLB4B.noLowTwoRankSectionFor_lowTwoRank
  have hlist : TheoremThreeList S :=
    TheoremThreeList.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
      (hSLB L hL.kGroup hL.evenRank_le H S hq π hπ).1
  have hlt : ∀ p : ℕ, p.Prime → 3 < p → localRank p S < 3 := by
    intro p hp hp3
    let e : H ⧸ π.ker ≃* S := QuotientGroup.quotientKerEquivOfSurjective π hπ
    have hq' : CFSG.IsQuasisimple (H ⧸ π.ker) := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq
    have hl := Item41Narrow.item4_1LargeAll_of_griess
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds L hL H π.ker
      (CFSG.RankThree.Coprime.layer_eq_top_of_isQuasisimple hq') p hp hp3
    rwa [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hp] at hl
  exact list42_of_theoremThreeList_of_lt hlt PartTwo.Census.bridgeSp6Two
    PartTwo.Census.bridgeSp6Four PartTwo.Census.bridgeSp8Two PartTwo.Census.bridgeOmega8PlusTwo
    PartTwo.Census.bridgeOmega8MinusTwo spinLargePrimeRankThree hlist

end List

end CFSG.RankThree.PartTwo.Sec4.Census
