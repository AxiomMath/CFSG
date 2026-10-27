module

public import CFSG.Monster.SteinbergMCatalogInner
public import CFSG.Sporadic.Bridge.MonsterModelsGriess

public section

namespace CFSG.Sporadic.MI301

open CFSG.Monster.Existence


theorem nonempty_mGriess_equiv_sporadicM :
    Nonempty (MGriess ≃* (TauCeti.CFSGIndex.sporadic .M).Group) := by
  obtain ⟨e₀⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  obtain ⟨e₁⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_tauCeti
  exact ⟨e₀.trans e₁⟩

theorem mGriess_mulAut_eq_conj (α : MulAut MGriess) : ∃ g : MGriess, α = MulAut.conj g := by
  obtain ⟨e₀⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  haveI : IsSimpleGroup MGriess := MGriess_finite_nonabelian_simple.2.1
  obtain ⟨g, hg⟩ := CFSG.ComponentClassification.BMCase.catalogM_mulAut_mem_inner MGriess
    inferInstance ⟨e₀⟩ α
  exact ⟨g, hg.symm⟩

end CFSG.Sporadic.MI301
