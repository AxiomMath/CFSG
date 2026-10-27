module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ForceLieTools
public import CFSG.GH74.KGroups.U33

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups.U33

private def u33Y : Equiv.Perm (Fin 28) := pb * pa⁻¹ * pb⁻¹ * pa⁻¹ * pb⁻¹ * (pa * pb⁻¹) ^ 4

private def u33G : Equiv.Perm (Fin 28) := pb⁻¹ * pa * pb⁻¹ * (pa⁻¹ * pb⁻¹) ^ 2 * pa * pb⁻¹

private theorem u33_facts : pa ^ 3 = 1 ∧ u33Y ^ 3 = 1 ∧
    pa * (u33Y * pa * u33Y⁻¹) = u33Y * pa * u33Y⁻¹ * pa ∧ pa * u33Y ≠ u33Y * pa ∧
    u33G * pa * u33G⁻¹ = pa⁻¹ ∧ u33G * u33Y * u33G⁻¹ = u33Y⁻¹ := by
  decide +kernel

private theorem u33_mem : pa ∈ QP.originalSubgroup ∧ u33Y ∈ QP.originalSubgroup ∧
    u33G ∈ QP.originalSubgroup := by
  rw [QP_closure]
  have ha := pa_mem
  have hb := pb_mem
  set H := closure ({pa, pb} : Set (Equiv.Perm (Fin 28)))
  refine ⟨ha, ?_, ?_⟩
  · unfold u33Y
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hb (H.inv_mem ha))
      (H.inv_mem hb)) (H.inv_mem ha)) (H.inv_mem hb))
      (H.pow_mem (H.mul_mem ha (H.inv_mem hb)) 4)
  · unfold u33G
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem hb) ha)
      (H.inv_mem hb)) (H.pow_mem (H.mul_mem (H.inv_mem ha) (H.inv_mem hb)) 2)) ha)
      (H.inv_mem hb)

theorem forceRealPair_u33 : ForceRealPair ↥QP.originalSubgroup := by
  obtain ⟨ha, hb, hw, hab, hg, hk⟩ := u33_facts
  obtain ⟨m1, m2, m3⟩ := u33_mem
  exact ForceRealPair.of_mem _ m1 m2 m3 m3 ha hb hw hab hg hk

theorem forceRealPair_of_lieModel_PSU_three_three
    {Q : Type} [Group Q]
    (h : LieModel Q .PSU 3 3 1) : ForceRealPair Q := by
  obtain ⟨e⟩ := equiv_of_lieModel h
  exact forceRealPair_u33.of_mulEquiv e

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
