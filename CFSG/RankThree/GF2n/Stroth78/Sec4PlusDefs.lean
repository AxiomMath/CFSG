module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Defs

public section

namespace CFSG.RankThree.GF2n.Stroth78

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

@[expose] def ThreeFourPlus (S : Setting z E F) (a : G) : Prop :=
  ∃ α ∈ Eset S a, ∃ β ∈ Eset S a, orderOf (α * β) = 4

theorem threeFourPlus_or_orderOf_le_three (S : Setting z E F) (a : G)
    (h4 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 4) :
    ThreeFourPlus S a ∨ ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3 := by
  by_cases h : ThreeFourPlus S a
  · exact Or.inl h
  · refine Or.inr fun α hα α' hα' => ?_
    have h1 := h4 α hα α' hα'
    by_contra h3
    exact h ⟨α, hα, α', hα', by omega⟩

end CFSG.RankThree.GF2n.Stroth78
