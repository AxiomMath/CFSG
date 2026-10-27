module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16NineOpp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XDefs
public import CFSG.LocalAnalysis.UniquenessCase.Nine24R912L2
public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XPropB
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XPropD
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XPropE
import CFSG.LocalAnalysis.UniquenessCase.UCFront09s

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r9_24X_of_inputs (D : Data G) (h63 : UC6.R6_3 D) (h912 : F09.R912L2 D)
    (hR92 : F09.R92 D) (hB0 : KFactL2EvenThreeElts) (hKD : KFact913L2Even)
    (hK462 : UCK.K462) (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) : R9_24X D := by
  intro L P X n hL hLN hn hU hP hX hL2 hXp hA hSP
  have hperf : ⁅X, X⁆ = X := by
    rw [hX]
    exact derInf_isPerfect P
  have hopp : Opp 3 X = X := opp3_eq_self_of_isL2 hperf hL2
  have hXL : X ≤ L := by
    rw [hX]
    exact (Subgroup.map_subtype_le _).trans hP.2.1
  have hXM : X ≤ D.M := hXL.trans hL.1.le
  have hXne : X ≠ ⊥ := by
    intro hbot
    exact hXp (bot_unique (hbot ▸ CFSG.openPCoreOf_le 2 X))
  have hX3ne : Opp 3 X ≠ ⊥ := by
    rw [hopp]
    exact hXne
  have hidx : ∃ k : ℕ, ((Opp 3 X).subgroupOf X).index = 2 ^ k :=
    ⟨0, by rw [hopp, Subgroup.subgroupOf_self, Subgroup.index_top]; norm_num⟩
  have hA' : ∀ A ∈ F09.Inv9' D.M (Opp 3 X) 3, ⁅A, Opp 3 X⁆ ≤ pCoreOf 2 A := by
    rw [hopp]
    exact hA
  rcases r9_21Opp_of_r6_3 D h63 hSP X hX3ne hXM hXp hA' hidx with hU' | hY2
  · exact hU'
  · exfalso
    obtain ⟨D₃, hD₃X, hD₃⟩ := exists_card_eq_three_of_isL2 hL2
    have hD₃Opp : D₃ ≤ Opp 3 X := by
      rw [hopp]
      exact hD₃X
    obtain ⟨Y, H, S, hXY, hyp⟩ :=
      F09.exists_hyp97_of_mem_calY2_9 D hY2 hD₃Opp hD₃
    have hYmax : Y ∈ F09.calY2_9 D := hyp.2.1.prop
    obtain ⟨hnorm, hopY, hpc⟩ :=
      normal_opp_eq_of_mem_calY2 hB0 D hL hLN hn hU hP hX hL2 hXp hYmax hXY
    clear hX
    subst X
    have hSH : CFSG.ABGLocalTools.IsSylowOf 2 S H :=
      (h912 Y H D₃ S hyp (2 * n) (by omega) hL2 hpc).1
    have hHt : H ≠ ⊤ := ne_top_of_hyp97 D hyp
    have hH := eq_I9_sup_of_hyp97_L2_4n D hR92 hKD hyp rfl hn hL2 hperf hSH hnorm hHt
    have hI := I9_le_of_hyp97_L2_4n D hK462 hSch hyp rfl hn hL2 hperf hSH hnorm hHt
    obtain ⟨-, hHM, -⟩ := hyp.1.2.1
    refine hHM ?_
    rw [hH]
    exact sup_le hI inf_le_right

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
