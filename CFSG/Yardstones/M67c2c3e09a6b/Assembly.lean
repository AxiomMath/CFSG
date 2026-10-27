module

public import CFSG.Yardstones.M67c2c3e09a6b.Definitions
public import CFSG.Milestones.LC_GL_theorem_A
public import CFSG.Assembly.PretrichotomyRankFourReduction
public import CFSG.LocalAnalysis.GLTheoremB.NormalPlane
public import CFSG.LocalAnalysis.GLTheoremB.Prop98FinalReducedI19
public import CFSG.HardMathSupport.Solomon.LocalBalance.TheoremOneWired
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBFinal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveAClose
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.TransvFinal
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.PiGenOrthProved
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Final
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Input113
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Main
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreAssembly
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreDFour
public import CFSG.HardMathSupport.Timmesfeld.DFour.NonResidual44
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Final
public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Fi22
public import CFSG.HardMathSupport.Solomon.Proving.AutSixBalance
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TCAll
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Input19DeltaReduction
public import CFSG.HardMathSupport.Timmesfeld.Balance.DeltaLocal
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.Tables112Split
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.AltMain
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsMain

public section

namespace CFSG.Yardstones.M67c2c3e09a6b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem lc_gl_constructed_pretrichotomy_rank_four_of_consumer_yardstones
    (hA : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
      (∃ a b : G, a * b ≠ b * a) → CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G →
        4 ≤ CFSG.Open.evenRank G → ∀ m : ℕ, 4 ≤ m →
          (∀ q ∈ CFSG.Open.GLABeta (m + 1) G, CFSG.Open.GLAWeakCoreLocal G q) →
          (∀ q ∈ CFSG.Open.GLABeta m G,
            CFSG.Open.GLAWeakCoreLocal G q ∨ CFSG.Open.GLADeltaZero G q) →
          (∃ q ∈ CFSG.Open.GLABeta m G,
            CFSG.Open.GLATwoLocalRank q G = m ∧ CFSG.Open.GLADeltaZero G q) →
          ∃ p ∈ CFSG.Open.GLABeta m G, CFSG.Open.GLATwoLocalRank p G = m ∧
            CFSG.Open.GLADeltaZero G p ∧
            ((p = 3 ∧ CFSG.Open.GLAGF2Type G) ∨
              ∃ (B : Subgroup G) (x : G) (L : Subgroup G),
                CFSG.Open.GLASStar p B x L ∧ CFSG.Open.GLAStandardType p B x L))
    (h01 : KGroupTables) (h02 : LocalThreeBalanceSimpleFamilies) (h03 : LocalTwoBalanceThreeFive)
    (h04 : CFSG.HardMathSupport.Timmesfeld.LocalTwo.LocalTwoBalanceSimpleGtFive)
    (h05 : SporadicBpResiduals) (h06 : LieCentralizerResiduals)
    (h07 : PumpingUpConsumerFacts) (h08 : LThreeFourComponentFacts) (h09 : I271OpenFamilies)
    (h10 : I28_8.Th1J1Factorization)
    (h11 : CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs.InputUniq)
    (h12 : Sec6Out) (h13 : Prop95) (h14 : MovingAround) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
      (∃ a b : G, a * b ≠ b * a) → CFSG.Assembly.KProper CFSG.Assembly.InCatalog G →
        CFSG.Assembly.IsCharTwoType G → 4 ≤ CFSG.Assembly.evenRank G →
          (∀ p ∈ CFSG.Assembly.LargeEvenBeta 4 G,
            CFSG.Assembly.LargeEvenWeakCoreLocal G p) ∨ CFSG.Assembly.LargeEvenGF2Type G ∨
            ∃ p ∈ CFSG.Assembly.LargeEvenBeta 4 G,
              ∃ (B : Subgroup G) (x : G) (L : Subgroup G),
                CFSG.Assembly.LargeEvenSStar p B x L ∧
                  CFSG.Assembly.LargeEvenStandardType p B x L := by
  have hT112 :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.tables112_of_rest h01.tables112Rest
  have hTL2 := CFSG.HardMathSupport.Timmesfeld.Tables.Census.tableL2_unconditional
  have h2 : CFSG.HardMathSupport.Solomon.LocalBalance.LocalTwoBalanceGtFive :=
    CFSG.HardMathSupport.Timmesfeld.LocalTwo.localTwoBalanceGtFive_of_parts h04
      CFSG.HardMathSupport.Timmesfeld.LocalTwo.localTwoBalanceAltGtFive_proved
      CFSG.HardMathSupport.Timmesfeld.LocalTwo.localTwoBalanceLpEpsGtFive_proved
  have h3 : LocalThreeBalance :=
    localThreeBalance_of_simple_alt
      (localThreeBalanceSimple_of_families
        (CFSG.HardMathSupport.Timmesfeld.DefChar.localThreeBalanceDefChar_of_dFour
          (CFSG.HardMathSupport.Timmesfeld.DefChar.defCharInnerCoreFreeFamDFour_of_image
            CFSG.HardMathSupport.Timmesfeld.DFour.dFourPrimeCentralizerInImage_holds))
        h02.crossChar h02.sporadic)
      CFSG.HardMathSupport.Timmesfeld.Balance.Alt.localThreeBalanceAlt_proved
  have hOne : TheoremOne :=
    CFSG.HardMathSupport.Solomon.LocalBalance.theoremOne_of_localBalance_rest
      hT112 hTL2 ⟨h07.input14_33⟩ ⟨h07.input14_20_7, h11⟩ ⟨h07.gapFinalPumpup⟩
      h08.input25_3 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.bFiveNonCentral_holds
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.twoAPureKlein_three_Gmat
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat.twoATwoCommuting_five_Gmat
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus.monsterSevenClasses
      h05.j4Three h05.restPairs
      (input27_1K_of_familiesRest hT112 hTL2 tables112Types_holds
        ⟨h09.nnHatSixRank, i271AutBalanceAltSix_holds, h09.nnOther, h09.altDiv, h09.altNdiv,
          h09.chevPBal, h09.chevPExc, h09.sporGen, h09.autBalanceON, h09.onLow, h09.chevQL34,
          h09.chevQ⟩)
      h02.crossChar h02.sporadic h2 h3
      h03.crossCharThree h03.sporadicThree h03.crossCharFive h03.sporadicFive h12
      h06.semisimpleCent h06.defCharOuter h08.input25_2 h10 h01.kernelT
  have h98 : Prop98 :=
    prop98_final_reduced''''
      (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.input11_6_of_tables hT112
        h01.kernelT)
      (input19Delta_of_localBalance
        CFSG.HardMathSupport.Timmesfeld.Balance.deltaOfLocalBalance_proved h3) h13
      (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.input11_3_of_tables hT112 hTL2)
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.input27_9_3Transv_proved
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.inputPiGenOrth_proved
  intro G _ _ _ hnonab hK hchar he
  exact CFSG.Assembly.LargeEven.constructed_pretrichotomy_rank_four_of_theorem_a_of_theorem_b hA
    (theoremB_of_theoremOne_theoremTwo' hOne (h14 h98)) G hnonab hK hchar he


theorem pretrichotomy_of_yardstones
    (hA : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
      (∃ a b : G, a * b ≠ b * a) → CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G →
        4 ≤ CFSG.Open.evenRank G → ∀ m : ℕ, 4 ≤ m →
          (∀ q ∈ CFSG.Open.GLABeta (m + 1) G, CFSG.Open.GLAWeakCoreLocal G q) →
          (∀ q ∈ CFSG.Open.GLABeta m G,
            CFSG.Open.GLAWeakCoreLocal G q ∨ CFSG.Open.GLADeltaZero G q) →
          (∃ q ∈ CFSG.Open.GLABeta m G,
            CFSG.Open.GLATwoLocalRank q G = m ∧ CFSG.Open.GLADeltaZero G q) →
          ∃ p ∈ CFSG.Open.GLABeta m G, CFSG.Open.GLATwoLocalRank p G = m ∧
            CFSG.Open.GLADeltaZero G p ∧
            ((p = 3 ∧ CFSG.Open.GLAGF2Type G) ∨
              ∃ (B : Subgroup G) (x : G) (L : Subgroup G),
                CFSG.Open.GLASStar p B x L ∧ CFSG.Open.GLAStandardType p B x L))
    (h01 : KGroupTables) (h02 : LocalThreeBalanceSimpleFamilies) (h03 : LocalTwoBalanceThreeFive)
    (h04 : CFSG.HardMathSupport.Timmesfeld.LocalTwo.LocalTwoBalanceSimpleGtFive)
    (h05 : SporadicBpResiduals) (h06 : LieCentralizerResiduals)
    (h07 : PumpingUpFacts) (h08 : LThreeFourComponentFacts) (h09 : I271OpenFamilies)
    (h10 : I28_8.Th1J1Factorization)
    (h11 : CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs.InputUniq)
    (h12 : Sec6Out) (h13 : Prop95) (h14 : MovingAround) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
      (∃ a b : G, a * b ≠ b * a) → CFSG.Assembly.KProper CFSG.Assembly.InCatalog G →
        CFSG.Assembly.IsCharTwoType G → 4 ≤ CFSG.Assembly.evenRank G →
          (∀ p ∈ CFSG.Assembly.LargeEvenBeta 4 G,
            CFSG.Assembly.LargeEvenWeakCoreLocal G p) ∨ CFSG.Assembly.LargeEvenGF2Type G ∨
            ∃ p ∈ CFSG.Assembly.LargeEvenBeta 4 G,
              ∃ (B : Subgroup G) (x : G) (L : Subgroup G),
                CFSG.Assembly.LargeEvenSStar p B x L ∧
                  CFSG.Assembly.LargeEvenStandardType p B x L :=
  lc_gl_constructed_pretrichotomy_rank_four_of_consumer_yardstones hA h01 h02 h03 h04 h05 h06
    ⟨CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.input14_33_of_type h07.input14_33,
      h07.input14_20_7, h07.gapFinalPumpup⟩ h08 h09 h10 h11 h12 h13 h14

end CFSG.Yardstones.M67c2c3e09a6b
