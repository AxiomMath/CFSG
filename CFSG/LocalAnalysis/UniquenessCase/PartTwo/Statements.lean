module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def Thm1669 (D : Data G) : Prop :=
  ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3

theorem inCalV_of_hyp123 {M T V₀ V : Subgroup G} (h : Hyp123 M T V₀ V) : InCalV M V := by
  rcases h with h | h
  · exact h.1.1.1.1
  · exact h.1.2.1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
