module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem nineteen_glue_one (D : Data G) (h65 : S17.R17_65 D) : R19_glue_1 D := by
  intro V₀ V hV hbig hσ
  obtain ⟨p, hp⟩ := hσ
  obtain ⟨X, hX⟩ := h65 V₀ V hV p hp
  obtain ⟨L, hL, hXL⟩ := S17.mem_calLpStar.1 (S17.calL0Star_subset D p hX)
  exact ⟨p, L, hV, hp, hL, by rw [← hXL]; exact hX, hbig⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
