module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2OddKFactDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2OddIM
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2OddKCfg
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920ImgSyl
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XBasic
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R92b
public import CFSG.CGT.PushingUpLit.CGT6.SixThreeCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

variable {G : Type} [Group G] [Finite G]

@[expose] def R920L2OddY2 (D : Data G) : Prop :=
  ∀ (L D₃ A : Subgroup G) (n : ℕ), L ∈ calC D.M → IsL2 (Bar2 L) n → Odd n → 5 ≤ n →
    D₃ ≤ L → Nat.card D₃ = 3 → D₃ ∈ uniqueSet D.M → A ∈ uniqueSet D.M → A ≤ L →
    (Nat.card A).Prime → Nat.card A ∣ 2 ^ n - 1 → L ∉ F09.calY2_9 D

theorem r920L2OddY2_of_inputs (D : Data G)
    (h63c : CFSG.CGT.PushingUpLit.CGT6.AschbacherSixThreeCore) (h640 : UC6.R6_40_1 D)
    (hK32 : UCK.K32) (hK462 : UCK.K462) (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hKS : KFactShape92L2Odd) : R920L2OddY2 D := by
  intro L D₃ A n hL hL2 hodd h5 hD₃ hD₃c hD₃u hAu hAL hAp hAd hY2
  let c : R920CfgL2 D L D₃ A n := ⟨hL, hL2, hodd, h5, hD₃, hD₃c, hD₃u, hAL, hAp, hAd, hAu⟩
  obtain ⟨Y, H, S, -, h97, hY, hSH, -, -⟩ := exists_chain_of_mem_calY2 h63c h640 c hY2
  have hI : F09.I9 H ≤ D.M := I9_le_M_of_isL2_odd hK462 hSch c h97 hY hSH
  obtain ⟨hHsup, hShape⟩ := F09.r92_of_inputs hK32 hSch D Y H D₃ h97.1 (ne_top_of_hyp97 D h97)
  have hW : PartOne.Section9.wbar9 D Y H = ⊤ :=
    hKS (F09.Lbar9 Y H) hShape (PartOne.Section9.isCyclic_of_isPGroup_lbar9 h97.1) _ _ _ _ _
      (kCfgL2Odd_of_hyp97 c h97 hY hSH)
  have hL9 : F09.L9 Y H ≤ F09.I9 H ⊔ (H ⊓ D.M) :=
    L9_le_sup_of_wbar9_eq_top D h97.1.2.1.1 hW
  refine h97.1.2.1.2.1 ?_
  rw [hHsup]
  exact sup_le (hL9.trans (sup_le hI inf_le_right)) inf_le_right

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
