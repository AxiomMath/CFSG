module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC15TBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC15TFam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3GapTransvSmall
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16GapTransvectionSmall_holds (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) : S16GapTransvectionSmall D := by
  intro V L hV hC hS A hA g hAg hVg _ hrk
  have hk : D.k = 1 :=
    s15_Thirteen_k_eq_one_of_three_mem D hSg h1219 (by rw [hS.2.2]; exact Set.mem_singleton 3)
  obtain ⟨E, hEM, hE2, hfix, hmQ⟩ := s16c15t_bridge D hC hA hAg hVg hrk
  have h3 := s16c15t_rk_le_three D hC hS hEM hE2 (by omega)
  rw [hmQ]
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
