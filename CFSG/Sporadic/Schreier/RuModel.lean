module

public import CFSG.Sporadic.Schreier.RuIso
public import CFSG.Sporadic.Schreier.RuOuter

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.ComponentClassification.OuterAutomorphisms

theorem AT_Ru_model_Schreier :
    Group.IsSolvable (Outer CFSG.Blueprint.NativeSporadic.Ru) ∧
    ∀ (G : Type*) [Group G], Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Ru) →
      Group.IsSolvable (Outer G) := by
  have hP : Group.IsSolvable (Outer ruP) := AT_Ru_permutation_Schreier
  refine ⟨@solvable_of_equiv _ _ _ _ ruEquivP.symm hP, fun G _ ⟨e⟩ => ?_⟩
  exact @solvable_of_equiv _ _ _ _ (e.trans ruEquivP).symm hP

end CFSG.Sporadic.RuSchreier
