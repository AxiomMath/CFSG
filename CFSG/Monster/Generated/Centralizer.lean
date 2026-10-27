module

public import CFSG.Monster.Generated.Data
public import CFSG.Monster.Griess.AutFinite
public import CFSG.Monster.Parity.EqualsVisible

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Generated

open CFSG.Monster CFSG.Monster.Spin CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Parity

theorem Gvis_le_AutO : Gvis ≤ AutO := fun _ hf =>
  ⟨fun u v => (mem_Gvis_gmul hf u v).1, fun u v => (mem_Gvis_gmul hf u v).2⟩

theorem Hmat_le_AutO : Hmat ≤ AutO := Gvis_le_AutO

theorem Gmat_le_AutO : Gmat ≤ AutO := by
  rw [Gmat, Subgroup.closure_le]
  rintro f (hf | hf)
  · exact Gvis_le_AutO hf
  · rw [Set.mem_singleton_iff.1 hf]
    exact tauB_mem_AutO

instance : Finite Gmat :=
  Finite.of_injective (Subgroup.inclusion Gmat_le_AutO) (Subgroup.inclusion_injective _)

theorem finite_Gmat : Finite Gmat := inferInstance

theorem mem_Hmat_iff_of_mem_AutO {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ AutO) :
    g ∈ Hmat ↔ xmat * g = g * xmat := by
  rw [xmat_eq_xB]
  constructor
  · intro h
    have hc := ((rational_parity_centralizer_equals_visible.1 g).2 h).2.2
    exact LinearEquiv.ext fun u => (hc u).symm
  · intro h
    refine (rational_parity_centralizer_equals_visible.1 g).1 ⟨hg.1, hg.2, fun u => ?_⟩
    exact (LinearEquiv.congr_fun h u).symm

theorem Gmat_inf_centralizer_xmat : Gmat ⊓ Subgroup.centralizer {xmat} = Hmat := by
  ext g
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hg, hc⟩
    exact (mem_Hmat_iff_of_mem_AutO (Gmat_le_AutO hg)).2 hc.symm
  · intro hg
    exact ⟨Hmat_le_Gmat hg, ((mem_Hmat_iff_of_mem_AutO (Hmat_le_AutO hg)).1 hg).symm⟩

theorem Vmat_le_Hmat : Vmat ≤ Hmat := by
  intro g hg
  rw [← Gmat_inf_centralizer_xmat]
  refine ⟨Vmat_le_Gmat hg, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hx : xmat ∈ Vmat := mem_Vmat.2 (.inr (.inl rfl))
  exact mul_comm_of_mem_fourGroupB hg hx

theorem generated_rational_group_finite_centralizer :
    Gmat ≤ AutO ∧ Finite Gmat ∧ Gmat ⊓ Subgroup.centralizer {xmat} = Hmat ∧
    Vmat ≤ Hmat ∧ Nat.card Vmat = 4 ∧ IsElementaryAbelian 2 Vmat ∧
    (∀ g, g ∈ Vmat ↔ g = 1 ∨ g = xmat ∨ g = xmatTau ∨ g = xmatTau2) ∧
    xmat ≠ 1 ∧ xmatTau ≠ 1 ∧ xmatTau2 ≠ 1 ∧
    xmat ≠ xmatTau ∧ xmat ≠ xmatTau2 ∧ xmatTau ≠ xmatTau2 ∧
    tauB * xmat * tauB⁻¹ = xmatTau ∧ tauB * xmatTau * tauB⁻¹ = xmatTau2 ∧
    tauB * xmatTau2 * tauB⁻¹ = xmat := by
  refine ⟨Gmat_le_AutO, finite_Gmat, Gmat_inf_centralizer_xmat, Vmat_le_Hmat, card_fourGroupB,
    isElementaryAbelian_fourGroupB, fun _ => mem_Vmat, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [xmat_eq_xB, xmatTau_eq, xmatTau2_eq]
  · exact one_ne_xB.symm
  · exact one_ne_yB.symm
  · exact one_ne_zB.symm
  · exact xB_ne_yB
  · exact xB_ne_zB
  · exact yB_ne_zB
  · exact conj_tauB_xB
  · exact conj_tauB_yB
  · exact conj_tauB_zB

end CFSG.Monster.Generated
