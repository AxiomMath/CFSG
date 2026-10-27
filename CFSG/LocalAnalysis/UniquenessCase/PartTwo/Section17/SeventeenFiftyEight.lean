module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bar13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.F13

variable {G : Type} [Group G] [Finite G]

theorem calC_Lp_subset (D : Data G) (p : ℕ) : calC (Lp D p) ⊆ calC D.M := by
  rintro K ⟨hsub, hperf, hquasi⟩
  exact ⟨hsub.trans (.step (Lp_le_M D p) (s13_Lp_normal D.M p) (.refl D.M)), hperf, hquasi⟩

theorem seventeen_fiftyeight (D : Data G) {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h17_61 : R17_61At D V₀ V) (h17_63 : R17_63At D V₀ V) : R17_58At D V₀ V := by
  intro p hp54 L hL hshape
  have ctx : Ctx17_58 D V₀ V L p := ⟨hV, hp54, hL, hshape⟩
  obtain ⟨K, hKcal, hKne, hKnot⟩ := h17_61 L p ctx
  exact hKnot (h17_63 L p ctx K (calC_Lp_subset D p hKcal) hKne)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
