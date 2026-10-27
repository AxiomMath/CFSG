module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Choice
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Components
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Rank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Shape
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.PushUp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.SylowCent
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight

variable {G : Type} [Group G] [Finite G]

theorem mem_calC_of_uc1_4_10 {D : Data G} (he : evenRank G = 3) (h410 : UC1_4_10)
    {L N R : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hSz : IsSz (Bar2 L) n)
    (hN : N ∈ calMOf L) (hNM : N ≠ D.M)
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R (F08.CentOverO2 (D.M ⊓ N) L))
    (hNR : normalizer (R : Set G) ≤ D.M)
    (hA : ∀ A : Subgroup G, A ≤ L → (Nat.card A).Prime → Nat.card A ≠ 2 →
      normalizer (A : Set G) ≤ D.M) :
    L ∈ calC N := by
  have hNtop : N ≠ ⊤ := fun htop => hNM (D.maxLocal.2 N hN.1.1 (by rw [htop]; exact le_top))
  have heN : S17.eM N ≤ 3 := by
    unfold S17.eM
    refine csSup_le ⟨CFSG.Open.pRank 3 N, 3, Nat.prime_three, by norm_num, rfl⟩ ?_
    rintro m ⟨q, hq, hq2, rfl⟩
    exact (CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank q hq hq2 N
      hN.1.1).trans he.le
  have hLMN : L ∈ calC (D.M ⊓ N) := mem_calC_of_le hL (le_inf hL.1.le hN.2) inf_le_left
  exact h410 G N (D.M ⊓ N) L R n (D.standing.kProper.isKGroup N hNtop) heN inf_le_right hLMN
    (fstar_eq_pCoreOf_of_mem_calC (D.standing.charTwo D.M D.maxLocal.1) hL) hSz hR
    (fun x hx => ⟨hNR hx.2, hx.1⟩) fun A hAL hAp hA2 x hx => ⟨hA A hAL hAp hA2 hx.2, hx.1⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
