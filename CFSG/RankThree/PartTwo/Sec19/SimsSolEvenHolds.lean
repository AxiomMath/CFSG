module

public import CFSG.RankThree.PartOne.S12.SolTightHolds
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenTen
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenEight
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSix
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenGlue
public import CFSG.GF2Type.Smith1979.WidthFourKP
public import CFSG.GF2Type.Smith1979W3.WidthThreeHolds
import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmall6Card
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiHolds
public import CFSG.Adapters.ClassicalCatalogLinearUnitary
public import CFSG.RankThree.GF2n.Item310BridgesLie
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenEightTI
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenEightX

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.CGT.PushingUpLit.SolK

theorem evenN_ten_holds :
    EvenN 10 :=
  evenN_ten CFSG.RankThree.PartOne.SolIn.solomonTimmesfeldTight_holds

namespace Eight

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ}

theorem inCatalog_of_extraspecial_w4
    (hW4 : CFSG.GF2Type.Smith1979.Smith1979WidthFourCharTwoKP) (S : Setting G M X n) {z : G}
    (hzQ : z ∈ CFSG.Open.pCoreOf 2 M) (hz1 : z ≠ 1) (hz : orderOf z = 2)
    (hext : IsExtraspecialPGroup 2 ↥(CFSG.Open.pCoreOf 2 (CGOf z)))
    (hcard : Nat.card ↥(CFSG.Open.pCoreOf 2 (CGOf z)) = 2 ^ 9) :
    CFSG.Assembly.InCatalog G := by
  haveI := S.simple
  have hF := fstar_eq S hzQ hz1
  have h : CFSG.Yardstones.M3aba7dc4b8a8.Smith1979WidthFourList G :=
    hW4 G S.nonab S.charTwo S.kProper z hz (hF ▸ hext) (by rw [hF, hcard])
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact CFSG.ClassicalModels.statedClassicalModel_PSL_inCatalog_all G 6 2 1
      (CFSG.RankThree.GF2n.statedClassicalModel_of_lieModel (by decide) h)
  · exact CFSG.ClassicalModels.statedClassicalModel_PSU_inCatalog G 6 2 1
      (CFSG.RankThree.GF2n.statedClassicalModel_of_lieModel (by decide) h)
  · exact CFSG.RankThree.GF2n.pOmegaPlusBridge G 4 2 1 le_rfl
      (CFSG.RankThree.GF2n.statedClassicalModel_of_lieModel (by decide) h)
  · exact CFSG.RankThree.GF2n.pOmegaMinusBridge G 4 2 1 le_rfl
      (CFSG.RankThree.GF2n.statedClassicalModel_of_lieModel (by decide) h)
  · exact CFSG.RankThree.GF2n.chevalleyEvenBridge_trialityD4 G 1
      (CFSG.RankThree.GF2n.chevalleyExceptionalModel_of_lieModel (by decide) h)
  · exact CFSG.RankThree.GF2n.pOmegaPlusBridge G 4 3 1 le_rfl
      (CFSG.RankThree.GF2n.statedClassicalModel_of_lieModel (by decide) h)
  · exact CFSG.RankThree.GF2n.sporadicBridge_Co2 G h
  · exact CFSG.RankThree.GF2n.sporadicBridge_Co1 G h
  · exact CFSG.RankThree.GF2n.sporadicBridge_Th G h
  · exact CFSG.RankThree.GF2n.sporadicBridge_HN G h

end Eight

theorem evenN_eight_of_node_w4
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hW4 : CFSG.GF2Type.Smith1979.Smith1979WidthFourCharTwoKP)
    (hST : CFSG.CGT.PushingUpLit.SolK.SolomonTimmesfeldTight) : EvenN 8 := by
  intro G _ _ M X S
  obtain ⟨C⟩ := exists_cfg_of_setting S
  obtain ⟨D⟩ := C.exists_piData (by norm_num) (by decide)
  rcases C.card_Rc_le_two_eight D rfl hST hNode with h | hR
  · exact h
  by_cases hext : ∃ y : ↥(CFSG.Open.pCoreOf 2 M),
      barLen (Multiplicative.toAdd (D.piQ y)) = 4 ∧ ¬ CGOf (y : G) ≤ M
  · obtain ⟨y, hy4, hyM⟩ := hext
    obtain ⟨I, hIc, hI⟩ := exists_supp_of_len (Multiplicative.toAdd (D.piQ y))
    rw [hy4] at hIc
    rcases Eight.centralizer_le_M_or_extraspecial D hR y.2 hIc hI with h | ⟨hext, hcard, hord⟩
    · exact absurd h hyM
    · have hy1 : (y : G) ≠ 1 := Eight.x_ne_one D y.2 hIc (by norm_num) hI
      exact Eight.inCatalog_of_extraspecial_w4 hW4 S y.2 hy1 hord hext hcard
  · push Not at hext
    exact Eight.inCatalog_of_centInM C D hNode hR (Eight.centInM_of D hR hext)


theorem smith1979WidthFourCharTwoKP_of_widthsFourSix
    (h : CFSG.GF2Type.Smith1979WidthsFourSixCharTwoKP) :
    CFSG.GF2Type.Smith1979.Smith1979WidthFourCharTwoKP := by
  intro G _ _ _ hnonab hchar hK z hz hext hcard
  exact (h G hnonab hchar hK z hz hext 4 (by rw [hcard])).1 rfl

theorem evenN_eight_of_smith
    (hW4 : CFSG.GF2Type.Smith1979.Smith1979WidthFourCharTwoKP) : EvenN 8 :=
  evenN_eight_of_node_w4 SolSeven.nodeStatement_holds hW4
    CFSG.RankThree.PartOne.SolIn.solomonTimmesfeldTight_holds

theorem lit316SolomonEven_of_inputs
    (hStroth : CFSG.OddStandard.HigherRank.YamadaG23.StrothSigma6)
    (hFM : CFSG.OddStandard.HigherRank.YamadaG23.FooteMainL6)
    (hW4 : CFSG.GF2Type.Smith1979.Smith1979WidthFourCharTwoKP) : Lit316SolomonEven :=
  lit316SolomonEven_of_evenN
    (evenN_six_of_inputs cardRLeTwo_six hStroth hFM
      CFSG.Milestones.cl_lit_classical_involution_theorem_models yamakiSp62CharTwo_holds
      CFSG.GF2Type.Smith1979W3.smith1979WidthThreeCharTwoKP_holds)
    (evenN_eight_of_smith hW4) evenN_ten_holds

end CFSG.RankThree.PartTwo.Sec19.SolEven
