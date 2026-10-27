module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGResRowAt.smallE6_prime_three {G : Type} [Group G] {p : ℕ}
    {J X : Subgroup G} (hrow : GGResRowAt ggRowTwoNodeSmallE6 p J X) : p = 3 := by
  obtain ⟨labJ, labX, _, _, _, _, ⟨hRow, _⟩, htag⟩ := hrow
  rcases hRow with ⟨_, _, _, hX⟩ | ⟨_, _, _, hX⟩ | ⟨_, hp, _, _⟩ | ⟨_, hp, _, _⟩
  · subst hX
    simp at htag
  · subst hX
    simp at htag
  · exact hp
  · exact hp

@[expose] def GGResTwoNodeIndepSmallTwoThreeInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs x L _ J y K => p = 3 ∧
    ((GGResRowAt ggRowTwoNodeSmallE6 p J L ∧ x ∈ L) ∨
      (GGResRowAt ggRowTwoNodeSmallE6 p J K ∧ y ∈ K) ∨
      (GGResRowAt ggRowTwoNodeSmallA p J L ∧ x ∈ L ∧ GGResTwoNodeSideDatum p Bs K J) ∨
      (GGResRowAt ggRowTwoNodeSmallA p J K ∧ y ∈ K ∧ GGResTwoNodeSideDatum p Bs L J))

end CFSG.StandardType

end
