module

public import CFSG.Milestones.CAT_native_realization

public section

namespace CFSG.Milestones

open CFSG.Blueprint.NativeSporadic in
theorem fam_sporadic_native_converse
    (G : Type) [Group G] (hrep : NativeSporadicRep G) :
    Finite G ∧ Nontrivial G ∧ IsSimpleGroup G := by
  obtain ⟨s, ⟨e⟩⟩ := hrep
  obtain ⟨h1, h2, h3⟩ := cat_native_realization_sporadic s
  exact ⟨Finite.of_equiv _ e.symm.toEquiv, e.toEquiv.nontrivial, e.isSimpleGroup⟩

end CFSG.Milestones
