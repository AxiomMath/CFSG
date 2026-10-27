module

public import CFSG.Monster.SteinbergMCatalogNativeIso
public import CFSG.LocalAnalysis.ComponentClassification.SteinbergMGmatInner

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.BMCase

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Monster.Generated

theorem simple_presentation_M_model_schreier
    (hautH : ∀ β : MulAut Hmat, ∃ h : Hmat, β = MulAut.conj h) :
    ∀ (T : Type*) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
      Nonempty (T ≃* CFSG.Blueprint.NativeSporadic.M) → Group.IsSolvable (Outer T) := by
  intro T _ _ _ _ ⟨θ⟩
  exact isSolvable_outer_of_mulEquiv
    (MulEquiv.ofBijective _ (catalog_fM_comp_mulEquiv_bijective θ))
    (gmat_automorphisms_inner hautH)

end CFSG.ComponentClassification.BMCase
