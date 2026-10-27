module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4Rank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem s16c11_big_comba_card_le_of_perm {G : Type*} [Group G] {α : Type*} [Fintype α]
    (e : G ≃* Equiv.Perm α) (E : Subgroup G) (hsq : ∀ x ∈ E, x ^ 2 = 1) :
    Nat.card E ≤ 2 ^ (Fintype.card α / 2) := by
  have h : ∀ x ∈ e.mapSubgroup E, x ^ 2 = 1 := by
    intro x hx
    change x ∈ Subgroup.map e.toMonoidHom E at hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← map_pow, hsq y hy, map_one]
  have hb := CFSG.OddStandard.AltStdSmall4.card_le_two_pow_half_of_sq_eq_one
    (e.mapSubgroup E) h
  rwa [Subgroup.card_mapSubgroup] at hb

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
