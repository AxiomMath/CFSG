module

public import CFSG.Monster.SteinbergMGmatUnconditional

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.BMCase

open CFSG.ComponentClassification.OuterAutomorphisms

theorem catalogM_mulAut_mem_inner
    :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
      Nonempty (S ≃* CFSG.Blueprint.NativeSporadic.M) → ∀ α : MulAut S, α ∈ inner S := by
  intro S _ _ _ ⟨θ⟩ α
  obtain ⟨g, hg⟩ := inner_of_equiv
    (MulEquiv.ofBijective _ (catalog_fM_comp_mulEquiv_bijective θ))
    gmat_automorphisms_inner_unconditional α
  exact ⟨g, hg.symm⟩

end CFSG.ComponentClassification.BMCase
