module

public import CFSG.Monster.Griess.FourGroup
public import CFSG.Monster.Visible.Action

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Generated

open CFSG.Monster CFSG.Monster.Spin CFSG.Monster.Griess CFSG.Monster.Visible

@[expose] noncomputable def Gmat : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) :=
  Subgroup.closure ((Gvis : Set (SpaceB ≃ₗ[ℚ] SpaceB)) ∪ {tauB})

@[expose] noncomputable def Hmat : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) := Gvis

@[expose] noncomputable def Qmat : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) := rhoQ

@[expose] noncomputable def xmat : SpaceB ≃ₗ[ℚ] SpaceB := rhoEquiv zQ

@[expose] noncomputable def xmatTau : SpaceB ≃ₗ[ℚ] SpaceB := tauB * xmat * tauB⁻¹

@[expose] noncomputable def xmatTau2 : SpaceB ≃ₗ[ℚ] SpaceB := tauB ^ 2 * xmat * (tauB ^ 2)⁻¹

@[expose] noncomputable def Vmat : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) := fourGroupB

theorem xmat_eq_xB : xmat = xB := rhoEquiv_zQ

theorem xmatTau_eq : xmatTau = yB := by rw [xmatTau, xmat_eq_xB, yB]

theorem xmatTau2_eq : xmatTau2 = zB := by rw [xmatTau2, xmat_eq_xB, zB]

theorem mem_Vmat {g : SpaceB ≃ₗ[ℚ] SpaceB} :
    g ∈ Vmat ↔ g = 1 ∨ g = xmat ∨ g = xmatTau ∨ g = xmatTau2 := by
  rw [xmat_eq_xB, xmatTau_eq, xmatTau2_eq]
  exact rational_triality_four_group.2.2.2.2.2.1 g

theorem Hmat_le_Gmat : Hmat ≤ Gmat := fun _ hg =>
  Subgroup.subset_closure (Set.mem_union_left _ hg)

theorem tauB_mem_Gmat : tauB ∈ Gmat := Subgroup.subset_closure (Set.mem_union_right _ rfl)

theorem Qmat_le_Hmat : Qmat ≤ Hmat := rhoQ_le_Gvis

theorem xmat_mem_Qmat : xmat ∈ Qmat := mem_rhoQ.2 ⟨zQ, rfl⟩

theorem Vmat_le_Gmat : Vmat ≤ Gmat := by
  intro g hg
  rcases mem_Vmat.1 hg with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact Hmat_le_Gmat (Qmat_le_Hmat xmat_mem_Qmat)
  · exact mul_mem (mul_mem tauB_mem_Gmat (Hmat_le_Gmat (Qmat_le_Hmat xmat_mem_Qmat)))
      (inv_mem tauB_mem_Gmat)
  · exact mul_mem (mul_mem (pow_mem tauB_mem_Gmat 2)
      (Hmat_le_Gmat (Qmat_le_Hmat xmat_mem_Qmat))) (inv_mem (pow_mem tauB_mem_Gmat 2))

theorem generated_rational_group_data :
    Gmat = Subgroup.closure ((Gvis : Set (SpaceB ≃ₗ[ℚ] SpaceB)) ∪ {tauB}) ∧ Hmat = Gvis ∧
    Qmat = rhoQ ∧ xmat = rhoEquiv zQ ∧ (zQ : GL SpinIdx ℚ) = -1 ∧
    xmatTau = tauB * xmat * tauB⁻¹ ∧ xmatTau2 = tauB ^ 2 * xmat * (tauB ^ 2)⁻¹ ∧
    (∀ g, g ∈ Vmat ↔ g = 1 ∨ g = xmat ∨ g = xmatTau ∨ g = xmatTau2) ∧
    Hmat ≤ Gmat ∧ tauB ∈ Gmat ∧ Qmat ≤ Hmat ∧ xmat ∈ Qmat ∧ Vmat ≤ Gmat :=
  ⟨rfl, rfl, rfl, rfl, coe_zQ, rfl, rfl, fun _ => mem_Vmat, Hmat_le_Gmat, tauB_mem_Gmat,
    Qmat_le_Hmat, xmat_mem_Qmat, Vmat_le_Gmat⟩

end CFSG.Monster.Generated
