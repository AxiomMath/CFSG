module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Context

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)

theorem N_mem_calMOf_T : c.N ∈ calMOf D.T := by
  have hN : c.N ∈ calMOf (c.L ⊔ D.T) := by
    rw [c.hN]
    simp
  exact ⟨hN.1, le_sup_right.trans hN.2⟩

theorem N_ne_M : c.N ≠ D.M := by
  intro hNM
  have hLcal : c.L ∈ calL D.T D.M := c.hL.1
  have hH : c.L ⊔ D.T ∈ hSet D.T D.M := hLcal.2.2.1
  have hN : c.N ∈ calMOf (c.L ⊔ D.T) := by
    rw [c.hN]
    simp
  exact hH.2.1 (hNM ▸ hN.2)

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22
