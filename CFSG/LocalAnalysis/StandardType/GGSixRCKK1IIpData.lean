module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.A8Cent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes

public section

namespace CFSG.StandardType.RCKK1IIp

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.RCKC1

@[expose] def rA8 : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def sA8 : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def vA8 : Subgroup (alternatingGroup (Fin 8)) := Subgroup.closure {rA8, sA8}

private def rckIIpData_T : Subgroup (alternatingGroup (Fin 8)) where
  carrier := ({1, rA8, sA8, rA8 * sA8} : Set (alternatingGroup (Fin 8)))
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;> decide
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> decide

private theorem rckIIpData_mem_T_iff (x : alternatingGroup (Fin 8)) :
    x ∈ rckIIpData_T ↔ x = 1 ∨ x = rA8 ∨ x = sA8 ∨ x = rA8 * sA8 := by
  show x ∈ ({1, rA8, sA8, rA8 * sA8} : Set (alternatingGroup (Fin 8))) ↔ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

private def rckIIpData_j1 : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 1 2 * Equiv.swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def rckIIpData_j2 : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 1 3 * Equiv.swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private theorem rckIIpData_vA8_eq_T : vA8 = rckIIpData_T := by
  apply le_antisymm
  · change Subgroup.closure ({rA8, sA8} : Set (alternatingGroup (Fin 8))) ≤ rckIIpData_T
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact (rckIIpData_mem_T_iff rA8).mpr (Or.inr (Or.inl rfl))
    · exact (rckIIpData_mem_T_iff sA8).mpr (Or.inr (Or.inr (Or.inl rfl)))
  · intro x hx
    have hx' : x = 1 ∨ x = rA8 ∨ x = sA8 ∨ x = rA8 * sA8 := (rckIIpData_mem_T_iff x).mp hx
    rcases hx' with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

private theorem rckIIpData_mem_vA8_iff (x : alternatingGroup (Fin 8)) :
    x ∈ vA8 ↔ x = 1 ∨ x = rA8 ∨ x = sA8 ∨ x = rA8 * sA8 := by
  rw [rckIIpData_vA8_eq_T]
  exact rckIIpData_mem_T_iff x

private theorem rckIIpData_card_T : Nat.card rckIIpData_T = 4 := by
  let s : Finset (alternatingGroup (Fin 8)) := {1, rA8, sA8, rA8 * sA8}
  have H : ∀ x, x ∈ s ↔ x ∈ (rckIIpData_T : Set (alternatingGroup (Fin 8))) := by
    intro x
    have h1 : x ∈ s ↔ x = 1 ∨ x = rA8 ∨ x = sA8 ∨ x = rA8 * sA8 := by
      simp only [s, Finset.mem_insert, Finset.mem_singleton]
    exact h1.trans (rckIIpData_mem_T_iff x).symm
  letI : Fintype ↑(rckIIpData_T : Set (alternatingGroup (Fin 8))) := Fintype.ofFinset s H
  rw [show Nat.card ↥rckIIpData_T =
      Nat.card ↑(rckIIpData_T : Set (alternatingGroup (Fin 8))) from rfl]
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_ofFinset s H]
  decide

theorem card_centralizer_rA8 :
    Nat.card (Subgroup.centralizer ({rA8} : Set (alternatingGroup (Fin 8)))) = 96 := by
  have hs : (rA8 : Equiv.Perm (Fin 8)).cycleType = {2, 2} := by
    change (Equiv.swap (0 : Fin 8) (1 : Fin 8) *
      Equiv.swap (2 : Fin 8) (3 : Fin 8)).cycleType = {2, 2}
    have hdisj : Equiv.Perm.Disjoint (Equiv.swap (0 : Fin 8) 1) (Equiv.swap (2 : Fin 8) 3) := by
      intro x
      fin_cases x <;> decide
    rw [Equiv.Perm.Disjoint.cycleType_mul hdisj,
      (Equiv.Perm.isCycle_swap (by decide : (0 : Fin 8) ≠ 1)).cycleType,
      (Equiv.Perm.isCycle_swap (by decide : (2 : Fin 8) ≠ 3)).cycleType,
      Equiv.Perm.card_support_swap (by decide : (0 : Fin 8) ≠ 1),
      Equiv.Perm.card_support_swap (by decide : (2 : Fin 8) ≠ 3)]
    norm_num [Multiset.replicate_succ]
  exact CFSG.EvenSporadicStandard.HNRecog.Section3.y4a_card_Gx_two_two hs

theorem rckIIp_A8_four :
    rA8 ∈ vA8 ∧ rA8 ≠ 1 ∧ IsElemAbelian 2 vA8 ∧ Nat.card vA8 = 4 ∧
      (∀ v ∈ vA8, v ≠ 1 → ∃ j : alternatingGroup (Fin 8), v = j * rA8 * j⁻¹) := by
  refine ⟨Subgroup.subset_closure (by simp), ?_, ?_, ?_, ?_⟩
  · decide
  · change IsMulCommutative vA8 ∧ ∀ x ∈ vA8, x ^ 2 = 1
    constructor
    · refine ⟨⟨?_⟩⟩
      intro x y
      apply Subtype.ext
      change (x : alternatingGroup (Fin 8)) * (y : alternatingGroup (Fin 8)) =
        (y : alternatingGroup (Fin 8)) * (x : alternatingGroup (Fin 8))
      have hx := x.property
      have hy := y.property
      rw [rckIIpData_mem_vA8_iff] at hx hy
      rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;>
        rw [hx, hy] <;> decide
    · intro x hx
      rw [rckIIpData_mem_vA8_iff] at hx
      rcases hx with hx | hx | hx | hx <;> rw [hx] <;> decide
  · rw [rckIIpData_vA8_eq_T]
    exact rckIIpData_card_T
  · intro v hv hv1
    rw [rckIIpData_mem_vA8_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact absurd rfl hv1
    · exact ⟨1, by decide⟩
    · exact ⟨rckIIpData_j1, by decide⟩
    · exact ⟨rckIIpData_j2, by decide⟩

end CFSG.StandardType.RCKK1IIp
