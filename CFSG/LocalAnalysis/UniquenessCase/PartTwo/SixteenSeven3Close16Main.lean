module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Cent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Cover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Norm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Sixteen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r16_16_of_r119 (D : Data G) (h12 : R16_12 D) (h13b : R16_13_2 D)
    (hSg : UC6S846.SigmaStd D) (h119 : F11.R119 D) (h127 : R127 D) (h61 : UC6.R6_1 D)
    (h78 : R7_8At3 D) (h921 : R9_21Opp D)
    (h96 : UC9R96.R9_6At7 D) : R16_16 D := by
  intro V₀ V L hV hc hL
  obtain ⟨hnot, rfl, -⟩ := h12 V₀ V L hV hc
  have hcase := s16c167_case_ln_four D hc hL (h13b ⊥ V L hV hc)
  have hS : Close16Setting D V L hV := ⟨hc, hcase⟩
  have hh : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  obtain ⟨z, hz, hz1⟩ := s16c167_exists_central_z D hh
  obtain ⟨Y, hY⟩ := close16_exists_Y h127 h119 hS
  have hSP := UC6S846.sp_of_mem_sig hSg (close16_not_solvable hS)
    (show 3 ∈ D.sig by rw [hS.shape.2.2]; exact Set.mem_singleton 3)
  have hMz : centralizer ({z} : Set G) ≤ D.M :=
    close16_centralizer_le hS hSP h61 h921 h96 hY hz hz1
      fun A hAY hA => close16_normalizer_seven_le h78 hSP hS hY hAY hA
  exact hnot ((s16c167_centralizer_cClos_le D (s15_13A_le_T hh) hz D.k).trans hMz)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
