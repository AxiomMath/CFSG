module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3OmegaB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920Chain
public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920IM
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KCfg
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KFactHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920ImgSyl
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XBasic
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R92b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_R920L28_of_inputs (D : Data G)
    (h61 : UC6.R6_1 D) (h63 : CFSG.CGT.PushingUpLit.CGT6.AschbacherSixThreeCore)
    (h640 : UC6.R6_40_1 D) (hK32 : UCK.K32) (hK46 : UCK.K46Semireg)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) : s16h_e3_R920L28 D := by
  intro h3 L₀ D₃ A hL hLM hL2 hO hD₃ hD₃c hD₃u hA hAc hAu
  let c : R920Cfg D L₀ D₃ A := ⟨hL, hLM, hL2, hO, hD₃, hD₃c, hD₃u, hA, hAc, hAu⟩
  by_contra hnot
  have hex : ∃ N : Subgroup G, rankThreeIsMaxTwoLocal N ∧ L₀ ≤ N ∧ N ≠ D.M := by
    by_contra h
    refine hnot (Set.eq_singleton_iff_unique_mem.2 ⟨⟨D.maxLocal, hLM⟩, ?_⟩)
    intro N hN
    by_contra hNe
    exact h ⟨N, hN.1, hN.2, hNe⟩
  obtain ⟨Y, H, S, -, h97, hY⟩ := c.exists_hyp97 h61 h3 hex
  have hSH : CFSG.ABGLocalTools.IsSylowOf 2 S H :=
    (c.chain_of_hyp97 h63 h640 h97 hY).syl_H
  have hI : F09.I9 H ≤ D.M := c.I9_le_M hSch hK46 h97 hY hSH
  have hHt : H ≠ ⊤ := ne_top_of_hyp97 D h97
  obtain ⟨hHsup, hShape⟩ := F09.r92_of_inputs hK32 hSch D Y H D₃ h97.1 hHt
  have hcyc : ∀ P : Subgroup (F09.Lbar9 Y H), IsPGroup 3 ↥P → IsCyclic ↥P :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.isCyclic_of_isPGroup_lbar9 h97.1
  have hW : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.wbar9 D Y H = ⊤ :=
    kFactShape92L28_holds (F09.Lbar9 Y H) hShape hcyc _ _ _
      (kCfgL28_of_hyp97 c h97 hY hSH)
  have hL9 : F09.L9 Y H ≤ F09.I9 H ⊔ (H ⊓ D.M) :=
    L9_le_sup_of_wbar9_eq_top D h97.1.2.1.1 hW
  refine h97.1.2.1.2.1 ?_
  rw [hHsup]
  exact sup_le (hL9.trans (sup_le hI inf_le_right)) inf_le_right

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
