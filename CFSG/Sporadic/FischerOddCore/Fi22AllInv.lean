module

public import CFSG.Sporadic.FischerOddCore.Fi22Sylow
public import CFSG.Sporadic.FischerOddCore.Fi22Unitary

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

theorem map_conj_inf_centralizer {G : Type*} [Group G] {P : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) (τ : G) :
    (P ⊓ Subgroup.centralizer {τ}).map (MulAut.conj g).toMonoidHom =
      P ⊓ Subgroup.centralizer {g * τ * g⁻¹} := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, ⟨hyP, hyc⟩, rfl⟩
    refine ⟨(Subgroup.mem_normalizer_iff.1 hg y).1 hyP, ?_⟩
    change g * y * g⁻¹ * (g * τ * g⁻¹) = g * τ * g⁻¹ * (g * y * g⁻¹)
    rw [show g * y * g⁻¹ * (g * τ * g⁻¹) = g * (y * τ) * g⁻¹ by group, hyc]
    group
  · rintro ⟨hxP, hxc⟩
    refine ⟨g⁻¹ * x * g, ⟨?_, ?_⟩, ?_⟩
    · apply (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * x * g)).2
      rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
    · have e : g⁻¹ * x * g * τ = g⁻¹ * (x * (g * τ * g⁻¹)) * g := by group
      rw [e, hxc]
      group
    · change g * (g⁻¹ * x * g) * g⁻¹ = x
      group

@[expose] def fi22CP_conj_equiv {G : Type*} [Group G] {P : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) (τ : G) :
    ↥(P ⊓ Subgroup.centralizer {τ}) ≃* ↥(P ⊓ Subgroup.centralizer {g * τ * g⁻¹}) :=
  ((P ⊓ Subgroup.centralizer {τ}).equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr (map_conj_inf_centralizer hg τ))

theorem oddCore_fi22CP_rep
    {k : ℕ} (hk : k < 6) :
    CFSG.oddCore ↥(fi22P ⊓ Subgroup.centralizer {fi22ExtRep k}) = ⊥ := by
  obtain ⟨-, h0, h1, h3, h4, h5, -⟩ := CTUC_Fi22_five_fixed_subgroups_odd_core_trivial
  interval_cases k
  · exact h0
  · exact h1
  · exact CTUC_Fi22_unitary_involution_centralizer_odd_core_trivial.2
  · exact h3
  · exact h4
  · exact h5

theorem CTUC_Fi22_all_involution_fixed_subgroups_odd_core_trivial :
    ∀ τ ∈ fi22R, orderOf τ = 2 →
      CFSG.oddCore ↥(fi22P ⊓ Subgroup.centralizer {τ}) = ⊥ := by
  intro τ hτ ho
  obtain ⟨k, hk, r, hr, hrτ⟩ := fi22R_involution_conj hτ ho
  have hrn := fi22R_le_normalizer hr
  have e := fi22CP_conj_equiv hrn τ
  rw [hrτ] at e
  exact oddCore_eq_bot_of_mulEquiv e.symm (oddCore_fi22CP_rep hk)

end CFSG.Sporadic.FischerOddCore
