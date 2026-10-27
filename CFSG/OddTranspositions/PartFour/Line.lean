module

public import CFSG.OddTranspositions.BlockGraph

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {G : Type*} [Group G] {D : Set G}

@[expose] def blockLine (D α β : Set G) : Set (Set G) :=
  {δ | δ ∈ blockClass α ∧ ∀ γ ∈ perp D α ∩ perp D β, δ ∈ perp D γ}

theorem mem_Dalpha_symm {D α γ : Set G} (hγ : γ ∈ Dalpha D α) (hα : α ⊆ D) :
    α ∈ Dalpha D γ :=
  ⟨mem_blockClass_comm.mpr hγ.1, hα, hγ.2.2.1.symm,
    fun a ha b hb => (hγ.2.2.2 b hb a ha).symm⟩

theorem mem_perp_symm {D α γ : Set G} (hγ : γ ∈ perp D α) (hα : α ⊆ D) :
    α ∈ perp D γ := by
  rw [mem_perp_iff] at hγ ⊢
  rcases hγ with h | rfl
  · exact Or.inl (mem_Dalpha_symm h hα)
  · exact Or.inr rfl

theorem left_mem_blockLine {α β : Set G} (hα : α ⊆ D) : α ∈ blockLine D α β := by
  refine ⟨mem_blockClass_self α, ?_⟩
  rintro γ ⟨hγα, -⟩
  exact mem_perp_symm hγα hα

theorem right_mem_blockLine {α β : Set G} (hβα : β ∈ blockClass α) (hβ : β ⊆ D) :
    β ∈ blockLine D α β := by
  refine ⟨hβα, ?_⟩
  rintro γ ⟨-, hγβ⟩
  exact mem_perp_symm hγβ hβ

end CFSG.OddTranspositions.PartFour
