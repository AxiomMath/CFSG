module

public import CFSG.YGroups.Y443.Native.Parabolic2Conj
public import CFSG.YGroups.Y443.Tri.Parabolic2Eval

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short CFSG.Open

theorem armSwapL_eq : armSwapL = ρL := rfl

theorem y443RhoM_axL_armSwapL {s : ℕ} (hs : s ≤ 11) :
    y443RhoM.toMonoidHom (axL s) = axL (armSwapL s) := by
  show y443RhoM (axL s) = _
  rw [y443RhoM_axL hs, armSwapL_eq]

theorem fM_comp_rhoM :
    fM.comp y443RhoM.toMonoidHom = (MulAut.conj Grho).toMonoidHom.comp fM :=
  fM_comp_of_axL fun _ hs => y443RhoM_axL_armSwapL hs

theorem fM_rhoM
    (m : MonsterY443Derived) : fM (y443RhoM m) = Grho * fM m * Grho⁻¹ :=
  DFunLike.congr_fun fM_comp_rhoM m

theorem fM_rhoM_op
    (m : MonsterY443Derived) :
    ((fM (y443RhoM m) : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) =
      wordLin rhoWord * ((fM m : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * (wordLin rhoWord)⁻¹ :=
  fM_apply_of_axL (fun _ hs => y443RhoM_axL_armSwapL hs) m

theorem injOn_fM_H'_iff :
    Set.InjOn fM y443H' ↔ Set.InjOn fM y443H := by
  rw [← injOn_comp_rho_iff fM, fM_comp_rhoM]
  constructor
  · intro h a ha b hb hab
    exact h ha hb (by show (MulAut.conj Grho) (fM a) = (MulAut.conj Grho) (fM b); rw [hab])
  · intro h a ha b hb hab
    exact h ha hb ((MulAut.conj Grho).injective hab)

theorem y443H'_map_fM :
    y443H'.map fM = (y443H.map fM).map (MulAut.conj Grho).toMonoidHom := by
  rw [← y443H_map_comp_rho fM, fM_comp_rhoM, ← Subgroup.map_map]

theorem y443H_map_fM_eq_conj :
    y443H.map fM = (y443H'.map fM).map (MulAut.conj Grho).toMonoidHom := by
  rw [Subgroup.map_map, ← fM_comp_rhoM, ← Subgroup.map_map, y443RhoM_map_H']

theorem y443R_map_fM_conj :
    (y443R.map fM).map (MulAut.conj Grho).toMonoidHom = y443R.map fM := by
  rw [Subgroup.map_map, ← fM_comp_rhoM, ← Subgroup.map_map, y443RhoM_map_R]

theorem natCard_y443H'_map_fM :
    Nat.card (y443H'.map fM) = Nat.card (y443H.map fM) := by
  rw [y443H'_map_fM]
  exact Subgroup.card_map_of_injective (MulAut.conj Grho).injective

theorem fM_y443C'_conj :
    fM y443C' = Grho * fM y443C * Grho⁻¹ := fM_rhoM y443C

theorem fM_y443X'_conj :
    fM y443X' = Grho * fM y443X * Grho⁻¹ := by
  rw [← y443RhoM_X]
  exact fM_rhoM y443X

theorem fM_y443X'_not_mem_iff :
    fM y443X' ∉ y443H'.map fM ↔ fM y443X ∉ y443H.map fM := by
  have e : fM y443X' = (MulAut.conj Grho).toMonoidHom (fM y443X) := fM_y443X'_conj
  rw [y443H'_map_fM, e]
  exact not_congr (Subgroup.mem_map_iff_mem (f := (MulAut.conj Grho).toMonoidHom)
    (MulAut.conj Grho).injective)

theorem fM_y443C'_op_eq :
    ((fM y443C' : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = evalGL sletP := by
  rw [fM_y443C'_eq_evalGL, sletP, armSwapL_eq]

theorem fM_y443C'_mem_shortClass :
    ((fM y443C' : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ shortClass := by
  rw [fM_y443C'_op_eq]
  exact cbarP_mem_shortClass

theorem fM_y443C_mul_y443C'_mem_shortClass :
    ((fM y443C : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * ((fM y443C' : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) ∈
      shortClass := by
  rw [fM_y443C'_op_eq, ← evalGL_slet_eq]
  exact cbar_mul_cbarP_mem_shortClass

theorem fM_y443C_comm_y443C' :
    ((fM y443C : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * ((fM y443C' : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) =
      ((fM y443C' : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * ((fM y443C : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) := by
  rw [fM_y443C'_op_eq, ← evalGL_slet_eq]
  exact cbar_comm_cbarP

theorem hedge_primed
    (hedge : ∀ h ∈ y443H.map fM, fM y443X * h * fM y443X ∈ y443H.map fM →
      ∃ k ∈ y443H, y443X * k * y443X ∈ y443H ∧ fM k = h) :
    ∀ h ∈ y443H'.map fM, fM y443X' * h * fM y443X' ∈ y443H'.map fM →
      ∃ k ∈ y443H', y443X' * k * y443X' ∈ y443H' ∧ fM k = h := by
  intro h' hh' hx'
  rw [y443H'_map_fM] at hh' hx'
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hh'
  rw [fM_y443X'_conj] at hx'
  have hx : fM y443X * h * fM y443X ∈ y443H.map fM := by
    have e : Grho * fM y443X * Grho⁻¹ * ((MulAut.conj Grho).toMonoidHom h) *
        (Grho * fM y443X * Grho⁻¹) =
        (MulAut.conj Grho).toMonoidHom (fM y443X * h * fM y443X) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e] at hx'
    exact (Subgroup.mem_map_iff_mem (f := (MulAut.conj Grho).toMonoidHom)
      (MulAut.conj Grho).injective).1 hx'
  obtain ⟨k, hk, hxk, hfk⟩ := hedge h hh hx
  refine ⟨y443RhoM k, y443RhoM_mem_H'_iff.2 hk, ?_, ?_⟩
  · rw [← y443RhoM_X, ← map_mul, ← map_mul]
    exact y443RhoM_mem_H'_iff.2 hxk
  · rw [fM_rhoM, hfk]
    rfl

theorem hd_primed_fM_of_hd
    (hd : fM y443C * (fM y443X * fM y443C * fM y443X) ≠
      (fM y443X * fM y443C * fM y443X) * fM y443C) :
    fM y443C' * (fM y443X' * fM y443C' * fM y443X') ≠
      (fM y443X' * fM y443C' * fM y443X') * fM y443C' := by
  intro e
  refine hd ?_
  rw [fM_y443C'_conj, fM_y443X'_conj] at e
  have h1 : Grho * (fM y443C * (fM y443X * fM y443C * fM y443X)) * Grho⁻¹ =
      Grho * fM y443C * Grho⁻¹ * (Grho * fM y443X * Grho⁻¹ * (Grho * fM y443C * Grho⁻¹) *
        (Grho * fM y443X * Grho⁻¹)) := by group
  have h2 : Grho * ((fM y443X * fM y443C * fM y443X) * fM y443C) * Grho⁻¹ =
      Grho * fM y443X * Grho⁻¹ * (Grho * fM y443C * Grho⁻¹) * (Grho * fM y443X * Grho⁻¹) *
        (Grho * fM y443C * Grho⁻¹) := by group
  have e2 : Grho * (fM y443C * (fM y443X * fM y443C * fM y443X)) * Grho⁻¹ =
      Grho * ((fM y443X * fM y443C * fM y443X) * fM y443C) * Grho⁻¹ := by
    rw [h1, h2]
    exact e
  exact mul_left_cancel (mul_right_cancel e2)

theorem conj_fM_mem_Cgen_of_mem_H'
    {h : MonsterY443Derived} (hh : h ∈ y443H') :
    omegaP * ((fM h : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * omegaP⁻¹ ∈ Cgen := by
  refine conj_mem_Cgen_of_comm_cbarP (fM h).2 ?_
  rw [← fM_y443C'_op_eq]
  have := congrArg (fun m => ((fM m : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB)) (y443C'_comm_H' hh)
  simpa using this

theorem Hbar'_conj_le_Cgen :
    ((y443H'.map fM).map Gmat.subtype).map (MulAut.conj omegaP).toMonoidHom ≤ Cgen := by
  rintro _ ⟨_, ⟨x, ⟨h, hh, rfl⟩, rfl⟩, rfl⟩
  exact conj_fM_mem_Cgen_of_mem_H' hh

end CFSG.YGroups.Y443
