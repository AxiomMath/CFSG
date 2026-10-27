module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenForty
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem three_not_mem_sig_of_ctx17_40 {D : Data G} {V₀ V L : Subgroup G} {n : ℕ}
    (c : Ctx17_40 D V₀ V L n) (h35 : R17_35At D V₀ V)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) :
    3 ∉ D.sig := by
  intro h3
  have hns : ¬ Group.IsSolvable ↥D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC c.ctx.mem_calC
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg hns h3
  have hk2 : D.k = 2 := k_eq_two_of_ctx17_40 c h35
  have hk1 : D.k = 1 := by
    unfold Data.k
    simp [CFSG.LocalAnalysis.RankThreeUC.kParam, hsp]
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
