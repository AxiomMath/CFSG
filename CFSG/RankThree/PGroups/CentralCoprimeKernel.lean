module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PGroups

open Subgroup
open scoped Pointwise

variable {C : Type*} [Group C] [Finite C] {p : ℕ}

theorem sylow_normal_of_le_center_of_isPGroup_quotient (hp : p.Prime) {N : Subgroup C}
    [N.Normal] (hNZ : N ≤ center C) (hCN : IsPGroup p (C ⧸ N)) (Q : Sylow p C) :
    (Q : Subgroup C).Normal ∧ (N : Set C) * ((Q : Subgroup C) : Set C) = Set.univ ∧
      ∀ c : C, (∃ k : ℕ, orderOf c = p ^ k) → c ∈ (Q : Subgroup C) := by
  have : Fact p.Prime := ⟨hp⟩
  have hmap : (Q : Subgroup C).map (QuotientGroup.mk' N) = ⊤ := by
    rw [← Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective N) Q]
    exact ((Sylow.mapSurjective (QuotientGroup.mk'_surjective N) Q).3
      (hCN.to_subgroup ⊤) le_top).symm
  have htop : N ⊔ (Q : Subgroup C) = ⊤ := by
    rw [← QuotientGroup.comap_map_mk', hmap, comap_top]
  have hQ : (Q : Subgroup C).Normal := by
    refine normalizer_eq_top_iff.1 (eq_top_iff.2 (htop ▸ sup_le ?_ le_normalizer))
    exact hNZ.trans (center_le_normalizer _)
  refine ⟨hQ, by rw [← normal_mul, htop, coe_top], fun c ⟨k, hk⟩ => ?_⟩
  have hc : IsPGroup p (zpowers c) := IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  have hsup := Q.3 (Q.2.to_sup_of_normal_left hc) le_sup_left
  exact hsup ▸ mem_sup_right (mem_zpowers c)

end CFSG.RankThree.PGroups
