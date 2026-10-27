module

public import CFSG.Quasithin.H13.GoldschmidtU3RankLGrp
public import CFSG.Quasithin.H13.U3Local1332
public import CFSG.Quasithin.H13.U3S135Gen
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def ExcludedMinimalOvergroupTwoRankBoundL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L H : Subgroup G), QTH13 G T L →
    centralizer (quasithinOmegaOneCenter T : Set G) ≤ normalizer (L : Set G) → T ≤ H →
    ¬ Group.IsSolvable H → pCoreOf 2 H ≠ ⊥ → ¬ (T.subgroupOf H).Normal →
    ¬ H ≤ normalizer (L : Set G) → IsUniqueMaxOvergroup T (normalizer (L : Set G)) H →
    CFSG.pRank 2 (↥H ⧸ CFSG.pCore 2 ↥H) ≤ 4

theorem excludedMinimalOvergroupTwoRankBoundL_of
    (h1332 : Stmt13_3_2) (h1227 : Stmt12_2_7) : ExcludedMinimalOvergroupTwoRankBoundL := by
  intro G _ _ T L H hH hZM hTH hns hR hTn hHM huniq
  obtain ⟨V, hV⟩ := (h1332 G T L hH L hH.faithful).2.2.1.1
  have hyp : Hyp1223 G T L V := hyp1223_of h1332 hH hV
  have hstar : IsHStar T (normalizer (L : Set G)) H :=
    ⟨⟨hTH, hR⟩, hHM, fun Y hY hYH hYM => by
      by_contra hne
      exact hYM ((huniq.2.2 Y hY.1 (lt_of_le_of_ne hYH hne)).trans inf_le_right)⟩
  obtain ⟨hlie, -⟩ := (h1227 G T L V H hyp hZM hstar).2 hns
  obtain ⟨e0⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model _ hlie
  have h3 := pRank_quotient_pCore_le_three
    ((QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open _ 2).symm).trans e0)
  omega

theorem u3_local_uniqueness_and_escape_producer_of_1332_L (h1332 : Stmt13_3_2)
    (hconf : U3ConfinedCentralizerOvergroup) (hexcl : ExcludedMinimalOvergroupTwoRankBoundL) :
    U3LocalUniquenessEscapeProducer := by
  intro G _ _ T L V z hH hU3 hF
  obtain ⟨hMtop, hVM, hTI, -, -⟩ := u3_selected_local_normalizer_and_TI_of_1332 h1332 hH hF
  refine ⟨hMtop, hVM, fun m hm => hTI m hm, fun hz => ?_⟩
  obtain ⟨-, -, -, -, -, -, hZM, -, ⟨H, ⟨hTH, hR, hHM⟩, hleast⟩, hmin⟩ :=
    hconf G T L V z hH hU3 hF hz
  obtain ⟨-, hns, -, -, hTn, huniq, h6⟩ := hmin H hTH hR hHM hleast
  have h4 := hexcl G T L H hH hZM hTH hns hR hTn hHM huniq
  omega

end CFSG.Quasithin.H13.U3
