module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem isU3_barSub_of_ctx17_40 {D : Data G} {V₀ V L : Subgroup G} {n : ℕ}
    (c : Ctx17_40 D V₀ V L n) (h35 : R17_35At D V₀ V) :
    IsU3 ↥(barSub V₀ V c.ctx.hyp125.isElemAbelian L) 2 := by
  obtain ⟨h1, -, -, hL⟩ := h35.2 L n c.ctx c.v0
  rwa [← hL] at h1

theorem k_eq_two_of_ctx17_40 {D : Data G} {V₀ V L : Subgroup G} {n : ℕ}
    (c : Ctx17_40 D V₀ V L n) (h35 : R17_35At D V₀ V) : D.k = 2 :=
  (h35.2 L n c.ctx c.v0).2.1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
