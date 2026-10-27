module

public import CFSG.RankThree.PartTwo.Sec21.FF84S33
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem mem_b (h : FF84Sec4 b L B K b₁ b₂) : b ∈ B := by
  rw [h.mono.2.1]; exact Subgroup.subset_closure (by simp)

theorem mem_b₁ (h : FF84Sec4 b L B K b₁ b₂) : b₁ ∈ B := by
  rw [h.mono.2.1]; exact Subgroup.subset_closure (by simp)

theorem mem_b₂ (h : FF84Sec4 b L B K b₁ b₂) : b₂ ∈ B := by
  rw [h.mono.2.1]; exact Subgroup.subset_closure (by simp)

theorem pow3_of_mem (h : FF84Sec4 b L B K b₁ b₂) {x : G} (hx : x ∈ B) : x ^ 3 = 1 := by
  haveI := h.mono.1.1
  exact elemPow_eq_one_of_isElementaryAbelian x hx

theorem comm_of_mem (h : FF84Sec4 b L B K b₁ b₂) {x y : G} (hx : x ∈ B) (hy : y ∈ B) :
    Commute x y :=
  commute_of_mem_elemAb h.mono.1.1 hx hy

theorem B_le_of_mem' (h : FF84Sec4 b L B K b₁ b₂) {M : Subgroup G} (hb : b ∈ M) (h1 : b₁ ∈ M)
    (h2 : b₂ ∈ M) : B ≤ M := by
  rw [h.mono.2.1]
  refine (Subgroup.closure_le _).2 ?_
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl <;> assumption

theorem card_B (h : FF84Sec4 b L B K b₁ b₂) : Nat.card B = 3 ^ 3 := h.mono.1.2

theorem not_B_le_pair (h : FF84Sec4 b L B K b₁ b₂) {x y : G} (hx : x ∈ B) (hy : y ∈ B)
    (hle : B ≤ Subgroup.closure ({x, y} : Set G)) : False :=
  not_le_closure_pair h.mono.1.2 (comm_of_mem h hx hy).eq (pow3_of_mem h hx) (pow3_of_mem h hy) hle

theorem b₁_notin_zpowers_b (h : FF84Sec4 b L B K b₁ b₂) : b₁ ∉ Subgroup.zpowers b := by
  intro hm
  refine not_B_le_pair h (mem_b h) (mem_b₂ h) (B_le_of_mem' h ?_ ?_ ?_)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp)) hm
  · exact Subgroup.subset_closure (by simp)

theorem b₂_notin_zpowers_b₁ (h : FF84Sec4 b L B K b₁ b₂) : b₂ ∉ Subgroup.zpowers b₁ := by
  intro hm
  refine not_B_le_pair h (mem_b h) (mem_b₁ h) (B_le_of_mem' h ?_ ?_ ?_)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp)) hm

theorem b₂_notin_zpowers_b (h : FF84Sec4 b L B K b₁ b₂) : b₂ ∉ Subgroup.zpowers b := by
  intro hm
  refine not_B_le_pair h (mem_b h) (mem_b₁ h) (B_le_of_mem' h ?_ ?_ ?_)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp)) hm

theorem b₂_notin_E (h : FF84Sec4 b L B K b₁ b₂) :
    b₂ ∉ Subgroup.closure ({b, b₁} : Set G) := by
  intro hm
  refine not_B_le_pair h (mem_b h) (mem_b₁ h) (B_le_of_mem' h ?_ ?_ hm)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem b_ne_one (h : FF84Sec4 b L B K b₁ b₂) : b ≠ 1 := fun he => by
  have := h.hyp.ord; rw [he] at this; simp at this

theorem b₁_ne_one (h : FF84Sec4 b L B K b₁ b₂) : b₁ ≠ 1 := fun he =>
  b₁_notin_zpowers_b h (he ▸ one_mem _)

theorem b₂_ne_one (h : FF84Sec4 b L B K b₁ b₂) : b₂ ≠ 1 := fun he =>
  b₂_notin_zpowers_b h (he ▸ one_mem _)

theorem bb₁_ne_one (h : FF84Sec4 b L B K b₁ b₂) : b * b₁ ≠ 1 := fun he =>
  b₁_notin_zpowers_b h (by
    have : b₁ = b⁻¹ := eq_inv_of_mul_eq_one_right he
    rw [this]; exact inv_mem (Subgroup.mem_zpowers b))

theorem bb₁inv_ne_one (h : FF84Sec4 b L B K b₁ b₂) : b * b₁⁻¹ ≠ 1 := fun he =>
  b₁_notin_zpowers_b h (by
    have : b₁⁻¹ = b⁻¹ := eq_inv_of_mul_eq_one_right he
    have h2 : b₁ = b := inv_injective this
    rw [h2]; exact Subgroup.mem_zpowers b)

theorem mul_mem_B (h : FF84Sec4 b L B K b₁ b₂) : b * b₁ ∈ B := mul_mem (mem_b h) (mem_b₁ h)

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
