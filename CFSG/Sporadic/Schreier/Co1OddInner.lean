module

public import CFSG.Sporadic.Schreier.Co1CatalogSchreier

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Sporadic.Co2Cert

theorem subsingleton_outer_of_inner {G : Type*} [Group G]
    (h : ∀ α : MulAut G, ∃ g : G, α = MulAut.conj g) : Subsingleton (Outer G) := by
  refine ⟨fun a b => ?_⟩
  induction a using QuotientGroup.induction_on with
  | H α =>
    induction b using QuotientGroup.induction_on with
    | H β =>
      rw [QuotientGroup.eq]
      obtain ⟨g, hg⟩ := h (α⁻¹ * β)
      exact ⟨g, hg.symm⟩

theorem inner_of_subsingleton_outer {G : Type*} [Group G] (h : Subsingleton (Outer G)) :
    ∀ α : MulAut G, ∃ g : G, α = MulAut.conj g := by
  intro α
  have h1 : (QuotientGroup.mk α : Outer G) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq_one_iff] at h1
  obtain ⟨g, hg⟩ := h1
  exact ⟨g, hg.symm⟩

noncomputable def co2PEquiv :
    Blueprint.NativeSporadic.Co2 ≃* co2P :=
  stabCo2Equiv.symm.trans stabPermEquiv

theorem full_automorphisms_inner_of_inputs
    (hCo2 : ∀ α : MulAut CFSG.Sporadic.Co2Cert.co2P, ∃ g : CFSG.Sporadic.Co2Cert.co2P,
      α = MulAut.conj g) :
    ∀ α : MulAut Blueprint.NativeSporadic.Co1, ∃ g : Blueprint.NativeSporadic.Co1,
      α = MulAut.conj g := by
  have hP : Subsingleton (Outer co2P) := subsingleton_outer_of_inner hCo2
  have hK : ∀ (K : Type) [Group K], K ≃* Blueprint.NativeSporadic.Co2 →
      Finite (Outer K) ∧ IsPGroup 2 (Outer K) ∧ Group.IsSolvable (Outer K) := by
    intro K _ e
    have e' : K ≃* co2P :=
      @MulEquiv.trans K Blueprint.NativeSporadic.Co2 co2P _ _ _ e co2PEquiv
    have : Subsingleton (Outer K) :=
      (@equivalence K co2P _ (Subgroup.toGroup co2P) e').toEquiv.subsingleton
    exact ⟨inferInstance, IsPGroup.of_subsingleton 2 (Outer K), inferInstance⟩
  obtain ⟨-, -, -, hdvd⟩ := catalog_schreier_of_inputs.{0} hK
  have hCo2' : Nat.card (Outer Blueprint.NativeSporadic.Co2) = 1 := by
    have : Subsingleton (Outer Blueprint.NativeSporadic.Co2) :=
      (@equivalence Blueprint.NativeSporadic.Co2 co2P Units.instGroup (Subgroup.toGroup co2P)
        co2PEquiv).toEquiv.subsingleton
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
  rw [hCo2', Nat.dvd_one] at hdvd
  exact @inner_of_subsingleton_outer Blueprint.NativeSporadic.Co1 Units.instGroup
    (Nat.card_eq_one_iff_unique.mp hdvd).1

end CFSG.Sporadic.Co1Schreier
