module

public import CFSG.Quasithin.H13.J4TypeFinal
public import CFSG.Sporadic.J4.QTOutChar

public section

namespace CFSG.Quasithin.ModJ4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
open CFSG.Quasithin.H13.J4 (IsAutTripleM22 IsTypeJ4Centralizer M22 center_M22 commutator_M22
  normal_mulAut_M22 mem_center_map_iff twoCentral_of_mulEquiv concreteJ4_typeJ4)

theorem tlc_z0_mem_center_P0 :
    eta uJ 11 1131 ∈ P0 ∧ ∀ y ∈ P0, y * eta uJ 11 1131 = eta uJ 11 1131 * y := by
  have hz : eta uJ 11 1131 ∈ Zc 1 := by
    rw [Zc_eq j4Facts.mat j4Facts 1 (by norm_num)]
    exact ⟨1131, by show 1131 ∈ ([0, 1131] : List ℕ); simp, rfl⟩
  refine ⟨hz.1, fun y hy => ?_⟩
  have h1 : eta uJ 11 1131 * y * (eta uJ 11 1131)⁻¹ * y⁻¹ = 1 := hz.2 y hy
  exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)).symm

theorem tlc_orderOf_z0 :
    orderOf (eta uJ 11 1131) = 2 := by
  have hsq : eta uJ 11 1131 * eta uJ 11 1131 = 1 := eta_sq (elem_uJ j4Facts.mat) 1131
  have hne : eta uJ 11 1131 ≠ 1 := by
    intro h
    have := eta_inj j4Facts.mat 1131 (by norm_num) 0 (by norm_num)
      (h.trans (eta_zero uJ 11).symm)
    omega
  exact orderOf_eq_prime (by rw [sq]; exact hsq) hne

theorem tlc_isTypeJ4Centralizer_z0 :
    IsTypeJ4Centralizer J (eta uJ 11 1131) := by
  obtain ⟨hzP, hzc⟩ := tlc_z0_mem_center_P0
  let P : Sylow 2 J :=
    Sylow.ofCard P0 (by rw [card_P0 j4Facts.mat j4Facts, card_J_factorization j4Facts])
  have hP : (P : Subgroup J) = P0 := rfl
  have hS : eta uJ 11 1131 ∈ (Subgroup.center (P : Subgroup J)).map (P : Subgroup J).subtype :=
    mem_center_map_iff.2 ⟨by rw [hP]; exact hzP, by rw [hP]; exact hzc⟩
  obtain ⟨z', hz'⟩ : ∃ y, (seedEquiv j4Facts.mat).symm (eta uJ 11 1131) = y := ⟨_, rfl⟩
  obtain ⟨hord, S', hS'⟩ := @twoCentral_of_mulEquiv J CFSG.Blueprint.NativeSporadic.J4
    (Subgroup.toGroup J) Units.instGroup _ _ _ _ hS (seedEquiv j4Facts.mat).symm hz'
  rw [tlc_orderOf_z0] at hord
  have h1 : IsTypeJ4Centralizer CFSG.Blueprint.NativeSporadic.J4 z' :=
    (concreteJ4_typeJ4).2.2.2.2 z' hord ⟨S', hS'⟩
  have hfinJ : Finite CFSG.Blueprint.NativeSporadic.J4 := (CFSG.Sporadic.J4.fam_j4_simplicity).1
  exact @IsTypeJ4Centralizer.of_mulEquiv CFSG.Blueprint.NativeSporadic.J4 J Units.instGroup
    (Subgroup.toGroup J) hfinJ z' (eta uJ 11 1131) h1 (seedEquiv j4Facts.mat)
    (by rw [← hz', MulEquiv.apply_symm_apply])

end CFSG.Quasithin.ModJ4
