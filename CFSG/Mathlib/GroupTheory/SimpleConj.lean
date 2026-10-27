module

public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG

variable {X : Type*} [Group X]

theorem le_of_forall_conj_mem_of_isSimpleGroup {J K : Subgroup X} (hJ : IsSimpleGroup J)
    (hK : ∀ j ∈ J, ∀ k ∈ K, j * k * j⁻¹ ∈ K) {g : X} (hgJ : g ∈ J) (hgK : g ∈ K)
    (hg1 : g ≠ 1) : J ≤ K := by
  have hn : (K.subgroupOf J).Normal := ⟨fun n hn k => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hK k k.2 n hn⟩
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hJ _ hn with h | h
  · have hmem : (⟨g, hgJ⟩ : J) ∈ K.subgroupOf J := hgK
    rw [h, Subgroup.mem_bot] at hmem
    exact absurd (congrArg Subtype.val hmem) hg1
  · intro j hj
    have hmem : (⟨j, hj⟩ : J) ∈ K.subgroupOf J := by
      rw [h]
      exact Subgroup.mem_top _
    exact hmem

end CFSG

end
