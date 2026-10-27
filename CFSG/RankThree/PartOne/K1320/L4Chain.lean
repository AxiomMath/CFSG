module

public import CFSG.RankThree.PartOne.K1320.L4Gen

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eM_mem_slB {i j : Fin 4} (h : i ≠ j) (c : K) : eM h c ∈ slB K i j :=
  Subgroup.subset_closure ⟨h, c, Or.inl rfl⟩

theorem eM_mem_slB_symm {i j : Fin 4} (h : i ≠ j) (c : K) : eM h.symm c ∈ slB K i j :=
  Subgroup.subset_closure ⟨h, c, Or.inr rfl⟩

theorem eM_mem_of_comm (H : Subgroup ↥(M8 K)) {i j l : Fin 4} (hij : i ≠ j) (hjl : j ≠ l)
    (hil : i ≠ l) {c d : K} (hc : eM hij c ∈ H) (hd : eM hjl d ∈ H) : eM hil (c * d) ∈ H := by
  rw [← comm_eM hij hjl hil c d]
  exact H.mul_mem (H.mul_mem (H.mul_mem hc hd) (H.inv_mem hc)) (H.inv_mem hd)

theorem slB_chain_sup (_h4 : 4 ≤ Nat.card K) :
    slB K 0 1 ⊔ slB K 1 2 ⊔ slB K 0 3 = ⊤ := by
  set H := slB K 0 1 ⊔ slB K 1 2 ⊔ slB K 0 3 with hH
  have m01 : ∀ c : K, eM (by decide : (0 : Fin 4) ≠ 1) c ∈ H := fun c =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (eM_mem_slB _ c))
  have m10 : ∀ c : K, eM (by decide : (1 : Fin 4) ≠ 0) c ∈ H := fun c =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (eM_mem_slB_symm (by decide : (0 : Fin 4) ≠ 1) c))
  have m12 : ∀ c : K, eM (by decide : (1 : Fin 4) ≠ 2) c ∈ H := fun c =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (eM_mem_slB _ c))
  have m21 : ∀ c : K, eM (by decide : (2 : Fin 4) ≠ 1) c ∈ H := fun c =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (eM_mem_slB_symm (by decide : (1 : Fin 4) ≠ 2) c))
  have m03 : ∀ c : K, eM (by decide : (0 : Fin 4) ≠ 3) c ∈ H := fun c =>
    Subgroup.mem_sup_right (eM_mem_slB _ c)
  have m30 : ∀ c : K, eM (by decide : (3 : Fin 4) ≠ 0) c ∈ H := fun c =>
    Subgroup.mem_sup_right (eM_mem_slB_symm (by decide : (0 : Fin 4) ≠ 3) c)
  have m02 : ∀ c : K, eM (by decide : (0 : Fin 4) ≠ 2) c ∈ H := fun c => by
    have h := eM_mem_of_comm H (by decide : (0 : Fin 4) ≠ 1) (by decide : (1 : Fin 4) ≠ 2)
      (by decide : (0 : Fin 4) ≠ 2) (m01 c) (m12 1)
    rwa [mul_one] at h
  have m20 : ∀ c : K, eM (by decide : (2 : Fin 4) ≠ 0) c ∈ H := fun c => by
    have h := eM_mem_of_comm H (by decide : (2 : Fin 4) ≠ 1) (by decide : (1 : Fin 4) ≠ 0)
      (by decide : (2 : Fin 4) ≠ 0) (m21 c) (m10 1)
    rwa [mul_one] at h
  have m13 : ∀ c : K, eM (by decide : (1 : Fin 4) ≠ 3) c ∈ H := fun c => by
    have h := eM_mem_of_comm H (by decide : (1 : Fin 4) ≠ 0) (by decide : (0 : Fin 4) ≠ 3)
      (by decide : (1 : Fin 4) ≠ 3) (m10 c) (m03 1)
    rwa [mul_one] at h
  have m31 : ∀ c : K, eM (by decide : (3 : Fin 4) ≠ 1) c ∈ H := fun c => by
    have h := eM_mem_of_comm H (by decide : (3 : Fin 4) ≠ 0) (by decide : (0 : Fin 4) ≠ 1)
      (by decide : (3 : Fin 4) ≠ 1) (m30 c) (m01 1)
    rwa [mul_one] at h
  have m23 : ∀ c : K, eM (by decide : (2 : Fin 4) ≠ 3) c ∈ H := fun c => by
    have h := eM_mem_of_comm H (by decide : (2 : Fin 4) ≠ 1) (by decide : (1 : Fin 4) ≠ 3)
      (by decide : (2 : Fin 4) ≠ 3) (m21 c) (m13 1)
    rwa [mul_one] at h
  have m32 : ∀ c : K, eM (by decide : (3 : Fin 4) ≠ 2) c ∈ H := fun c => by
    have h := eM_mem_of_comm H (by decide : (3 : Fin 4) ≠ 1) (by decide : (1 : Fin 4) ≠ 2)
      (by decide : (3 : Fin 4) ≠ 2) (m31 c) (m12 1)
    rwa [mul_one] at h
  refine eq_top_of_eM_mem H fun {i j} hij c => ?_
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact m01 c
  · exact m02 c
  · exact m03 c
  · exact m10 c
  · exact absurd rfl hij
  · exact m12 c
  · exact m13 c
  · exact m20 c
  · exact m21 c
  · exact absurd rfl hij
  · exact m23 c
  · exact m30 c
  · exact m31 c
  · exact m32 c
  · exact absurd rfl hij

end CFSG.RankThree.PartOne.K1320
