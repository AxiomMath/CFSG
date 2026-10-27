module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2Y2Normal
public import CFSG.LocalAnalysis.UniquenessCase.UC9R96Comm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16NineOpp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XPropD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XPropE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XKDHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XThreeElts
public import CFSG.LocalAnalysis.UniquenessCase.Nine24R912L2
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09s

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Blueprint (LieModel)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_pCoreOf_of_mem_inv9'_of_isL2 {M L B : Subgroup G} (hL : L ∈ calC M)
    {n : ℕ} (hL2 : IsL2 (Bar2 L) n) (hB : B ∈ F09.Inv9' M L 3) : ⁅B, L⁆ ≤ pCoreOf 2 B := by
  obtain ⟨hBM, hB3, hLB⟩ := hB
  exact UC9R96.comm_le_pCoreOf_of_mem_calC hL (opp3_eq_self_of_isL2 hL.2.1 hL2)
    (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2)
    (three_dvd_card_of_isL2 hL2) hBM hB3 hLB

theorem uniqueMax_or_mem_calY2_of_sp (D : Data G) (h63 : UC6.R6_3 D)
    (hsp : IsStronglyPEmbedded 3 D.M) {L : Subgroup G} {n : ℕ} (hL : L ∈ calC D.M)
    (hL2 : IsL2 (Bar2 L) n) : UniqueMax D.M L ∨ L ∈ F09.calY2_9 D := by
  have hopp : Opp 3 L = L := opp3_eq_self_of_isL2 hL.2.1 hL2
  have hLM : L ≤ D.M := CFSG.Open.IsSubnormal.le hL.1
  have hne : pCoreOf 2 L ≠ ⊥ :=
    pCoreOf_ne_bot_of_mem_calC D.standing.charTwo D.maxLocal.1 hL
  refine r9_21Opp_of_r6_3 D h63 hsp L ?_ hLM hne ?_ ?_
  · rw [hopp]
    intro h
    apply hne
    rw [eq_bot_iff, ← h]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 L
  · intro A hA
    rw [hopp] at hA ⊢
    exact commutator_le_pCoreOf_of_mem_inv9'_of_isL2 hL hL2 hA
  · exact ⟨0, by rw [hopp, Subgroup.subgroupOf_self, Subgroup.index_top]; norm_num⟩

theorem false_of_mem_calY2_of_isL2_even (hK462 : UCK.K462)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (D : Data G)
    (h912 : F09.R912L2 D) (hR92 : F09.R92 D) {L : Subgroup G} {n : ℕ}
    (hL : L ∈ calC D.M) (hn : 1 < n) (hL2 : IsL2 (Bar2 L) (2 * n))
    (hY2 : L ∈ F09.calY2_9 D) : False := by
  have hperf : ⁅L, L⁆ = L := hL.2.1
  have hopp : Opp 3 L = L := opp3_eq_self_of_isL2 hperf hL2
  obtain ⟨D₃, hD₃L, hD₃⟩ := exists_card_eq_three_of_isL2 hL2
  have hD₃Opp : D₃ ≤ Opp 3 L := by rw [hopp]; exact hD₃L
  obtain ⟨Y, H, S, hLY, hyp⟩ := F09.exists_hyp97_of_mem_calY2_9 D hY2 hD₃Opp hD₃
  have hYmax : Y ∈ F09.calY2_9 D := hyp.2.1.prop
  obtain ⟨hnorm, hopY, hpc⟩ :=
    normal_opp_eq_of_mem_calY2_of_calC kFactL2EvenThreeElts_holds D hL hL2 hYmax hLY
  have hL2' : IsL2 (Bar2 (Opp 3 Y)) (2 * n) := by rw [hopY]; exact hL2
  have hSH : CFSG.ABGLocalTools.IsSylowOf 2 S H :=
    (h912 Y H D₃ S hyp (2 * n) (by omega) hL2' hpc).1
  have hHt : H ≠ ⊤ := ne_top_of_hyp97 D hyp
  have hH := eq_I9_sup_of_hyp97_L2_4n D hR92 kFact913L2Even_holds hyp hopY hn hL2 hperf hSH
    hnorm hHt
  have hI := I9_le_of_hyp97_L2_4n D hK462 hSch hyp hopY hn hL2 hperf hSH hnorm hHt
  obtain ⟨-, hHM, -⟩ := hyp.1.2.1
  exact hHM (hH.le.trans (sup_le hI inf_le_right))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
