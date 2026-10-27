module

public import CFSG.RankThree.Chevalley.SteinbergBIWE8ClassesBase

public noncomputable section

namespace CFSG.RankThree.Chevalley.WeylE8

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.Timmesfeld.ExceptionalOrders

instance zpowers_z_normal : (Subgroup.zpowers z).Normal :=
  ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : Commute (z ^ k) g := ((Commute.zpow_left (z_mul_comm g) k))
    rw [← hc.eq, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩⟩

theorem card_roots : {α : L8 | IsRoot .E8 α}.ncard = 240 := by
  have h := ncard_setOf_isRoot_and (τ := .E8) fun _ => True
  simp only [and_true, decide_true, List.countP_true] at h
  rw [h]
  have := length_rootsL
  rwa [rootsL_eq, List.length_map] at this

end CFSG.RankThree.Chevalley.WeylE8
