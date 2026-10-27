
module

public import CFSG.Monster.B.Fischer.Fi22OuterBase
public import CFSG.Monster.B.Fischer.Fi22GraphCheckInputs
public import CFSG.Monster.B.Fischer.PinnedChainBase

@[expose] public noncomputable section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def fi22N0 : Set (Fin 3510) := {i | i ≠ 0 ∧ fi22OuterZ i = i}

@[expose] def fi22Graph : SimpleGraph (Fin 3510) :=
  SimpleGraph.fromEdgeSet {e | ∃ g ∈ fi22P, ∃ i ∈ fi22N0, e = s(g 0, g i)}

@[expose] def fi22U : Equiv.Perm (Fin 3510) := permOfArr 3510 fi22GraphOuterArr

@[expose] def fi22R : Subgroup (Equiv.Perm (Fin 3510)) :=
  Subgroup.closure (insert fi22U (fi22P : Set (Equiv.Perm (Fin 3510))))

theorem fi22N0_ends_ne {g : Equiv.Perm (Fin 3510)} {i : Fin 3510} (hi : i ∈ fi22N0) :
    g 0 ≠ g i := fun h => hi.1 (g.injective h).symm

theorem fi22Graph_adj (x y : Fin 3510) :
    fi22Graph.Adj x y ↔ ∃ g ∈ fi22P, ∃ i ∈ fi22N0,
      (g 0 = x ∧ g i = y) ∨ (g 0 = y ∧ g i = x) := by
  rw [fi22Graph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨g, hg, i, hi, he⟩, -⟩
    refine ⟨g, hg, i, hi, ?_⟩
    rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h2.symm, h1.symm⟩
  · rintro ⟨g, hg, i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨⟨g, hg, i, hi, rfl⟩, fi22N0_ends_ne hi⟩
    · exact ⟨⟨g, hg, i, hi, Sym2.eq_swap⟩, (fi22N0_ends_ne hi).symm⟩

end CFSG.Monster.B.Fischer
