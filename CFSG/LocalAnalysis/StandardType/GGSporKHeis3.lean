module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.HeisAction
import Mathlib.GroupTheory.Commutator.Basic
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.HardMathSupport.Solomon.Coordinator.B3B CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open scoped commutatorElement

variable {G : Type*} [Group G] {n : ℕ} {x y : Fin n → G} {z : G}

private theorem gkh3_cocycle_add_self (v : Fin (n + n) → ZMod 3) :
    heisCocycle (v + v) v = heisCocycle v v + heisCocycle v v := by
  unfold heisCocycle
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem heisSub3_pow_three (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) (hn : 0 < n) :
    ∀ q ∈ heisSub x y, q ^ 3 = 1 := by
  intro q hq
  obtain ⟨v, c, rfl⟩ := exists_heisNF h hy3 hn q hq
  have h1 := heisNF_mul h hy3 v v c c
  have h2 := heisNF_mul h hy3 (v + v) v (c + c + heisCocycle v v) c
  have hv : v + v + v = 0 := by
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    generalize v i = a
    revert a
    decide
  have hc : c + c + heisCocycle v v + c + heisCocycle (v + v) v = 0 := by
    rw [gkh3_cocycle_add_self]
    generalize heisCocycle v v = b
    generalize c = a
    revert a b
    decide
  rw [pow_three, ← mul_assoc, h1, h2, hv, hc, heisNF_zero_left, ZMod.val_zero, pow_zero]

theorem heisSub3_commutator (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) (hn : 0 < n) :
    ⁅heisSub x y, heisSub x y⁆ = Subgroup.zpowers z := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    have h1 : heisCoord h hy3 ⁅(⟨a, ha⟩ : ↥(heisSub x y)), ⟨b, hb⟩⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
    have h2 := (heisCoord_eq_one_iff h hy3 _).1 h1
    simpa [commutatorElement_def] using h2
  · rw [Subgroup.zpowers_le]
    have hx : x ⟨0, hn⟩ ∈ heisSub x y := x_mem_heisSub _
    have hy : y ⟨0, hn⟩ ∈ heisSub x y := y_mem_heisSub _
    have hxy := heisCfg_xy_same h ⟨0, hn⟩
    have hz : z = ⁅(x ⟨0, hn⟩)⁻¹, (y ⟨0, hn⟩)⁻¹⁆ := by
      rw [commutatorElement_def]
      have : z = (x ⟨0, hn⟩)⁻¹ * (y ⟨0, hn⟩)⁻¹ * x ⟨0, hn⟩ * y ⟨0, hn⟩ := by
        have h3 : x ⟨0, hn⟩ * y ⟨0, hn⟩ = y ⟨0, hn⟩ * x ⟨0, hn⟩ * z := hxy
        calc z = (x ⟨0, hn⟩)⁻¹ * (y ⟨0, hn⟩)⁻¹ * (y ⟨0, hn⟩ * x ⟨0, hn⟩ * z) := by group
          _ = (x ⟨0, hn⟩)⁻¹ * (y ⟨0, hn⟩)⁻¹ * (x ⟨0, hn⟩ * y ⟨0, hn⟩) := by rw [h3]
          _ = _ := by group
      rw [this]
      group
    rw [hz]
    exact Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hx) (Subgroup.inv_mem _ hy)

theorem heisSub3_inf_centralizer (h : HeisCfg 3 n x y z) (hy3 : ∀ i, y i ^ 3 = 1) (hn : 0 < n) :
    heisSub x y ⊓ Subgroup.centralizer (heisSub x y : Set G) = Subgroup.zpowers z := by
  apply le_antisymm
  · rintro q ⟨hq, hqC⟩
    exact mem_zpowers_of_forall_commute h hy3 hq fun i =>
      ⟨(Subgroup.mem_centralizer_iff.1 hqC (x i) (x_mem_heisSub i)).symm,
        (Subgroup.mem_centralizer_iff.1 hqC (y i) (y_mem_heisSub i)).symm⟩
  · rw [Subgroup.zpowers_le]
    refine ⟨z_mem h hn, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
    obtain ⟨v, c, rfl⟩ := exists_heisNF h hy3 hn q hq
    exact ((heisCfg_commute_z_heisNF h v c).eq).symm

end CFSG.StandardType.SporadicShape
