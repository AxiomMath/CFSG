module

import CFSG.Sporadic.Schreier.J1Centralizer
import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Sporadic.Schreier.J1Faithful

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG.Blueprint CFSG.Sporadic.Schreier

theorem center_J1_eq_bot :
    Subgroup.center NativeSporadic.J1 = ⊥ := by
  obtain ⟨-, -, -, h19, -⟩ := at_j1_image_pair_count
  have hsimp := CFSG.Sporadic.J1.isSimpleGroup_J1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center NativeSporadic.J1) with
    h | h
  · exact h
  · exfalso
    have hc : j1PermEquiv.symm ⟨j1A1, j1A1_mem⟩ * j1PermEquiv.symm ⟨j1A2, j1A2_mem⟩ =
        j1PermEquiv.symm ⟨j1A2, j1A2_mem⟩ * j1PermEquiv.symm ⟨j1A1, j1A1_mem⟩ :=
      (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top _) _).symm
    have hc' : j1A1 * j1A2 = j1A2 * j1A1 := by
      have := congrArg (fun y => ((j1PermEquiv y : j1P) : Equiv.Perm (Fin 3080))) hc
      simpa using this
    rw [hc', mul_inv_cancel_right, mul_inv_cancel, orderOf_one] at h19
    omega

theorem exists_orderOf_mul_inv_eq_nineteen_J1
    (φ : MulAut NativeSporadic.J1) (hφ : φ * φ = 1) (hφ1 : φ ≠ 1) :
    ∃ x : NativeSporadic.J1, orderOf (φ x * x⁻¹) = 19 := by
  obtain ⟨-, -, -, h19, -⟩ := at_j1_image_pair_count
  obtain ⟨g, rfl⟩ := at_j1_schreier.2.1 φ
  have hZ := center_J1_eq_bot
  have hg2 : g * g = 1 := by
    have hconj : MulAut.conj (g * g) = 1 := by rw [map_mul]; exact hφ
    have hc : g * g ∈ Subgroup.center NativeSporadic.J1 := by
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      have := congrArg (fun ψ : MulAut NativeSporadic.J1 => ψ y) hconj
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * (g * g) = g * g * y * (g * g)⁻¹ * (g * g) := by rw [this]
        _ = g * g * y := by group
    rw [hZ] at hc
    exact hc
  have hg1 : g ≠ 1 := fun h => hφ1 (by rw [h, map_one])
  have ho : orderOf g = 2 := orderOf_eq_prime (by rw [sq]; exact hg2) hg1
  have hou : orderOf ((j1PermEquiv g : j1P) : Equiv.Perm (Fin 3080)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ho]
  obtain ⟨c, hc, hcu⟩ := j1_involution_conj _ (j1PermEquiv g).2 hou
  have hmem : c * j1A2 * c⁻¹ ∈ j1P := j1P.mul_mem (j1P.mul_mem hc j1A2_mem) (j1P.inv_mem hc)
  refine ⟨j1PermEquiv.symm ⟨c * j1A2 * c⁻¹, hmem⟩, ?_⟩
  rw [← MulEquiv.orderOf_eq j1PermEquiv, ← Subgroup.orderOf_coe]
  have hval : ((j1PermEquiv (MulAut.conj g (j1PermEquiv.symm ⟨c * j1A2 * c⁻¹, hmem⟩) *
      (j1PermEquiv.symm ⟨c * j1A2 * c⁻¹, hmem⟩)⁻¹) : j1P) : Equiv.Perm (Fin 3080)) =
      MulAut.conj c (j1A1 * j1A2 * j1A1⁻¹ * j1A2⁻¹) := by
    simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply,
      Subgroup.coe_mul, Subgroup.coe_inv, hcu]
  rw [hval, MulEquiv.orderOf_eq, h19]

end CFSG.RankThree.PartTwo.Sec20
