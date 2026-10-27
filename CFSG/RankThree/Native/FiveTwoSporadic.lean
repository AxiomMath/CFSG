module

public import CFSG.RankThree.Native.FiveTwoCheck

public section

namespace CFSG.RankThree.Native

open CFSG.Blueprint

theorem mem_centralizer_zpowers_of_commute {S : Type*} [Group S] {z y : S} (h : z * y = y * z) :
    y ∈ Subgroup.centralizer (Subgroup.zpowers z : Set S) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro g ⟨k, rfl⟩
  exact ((Commute.zpow_left h k).eq : _)

theorem eleven_sporadic_models_commuting_five_and_two_elements {S : Type*} [Group S]
    (hS : Nonempty (S ≃* NativeSporadic.J3) ∨ Nonempty (S ≃* NativeSporadic.Co1) ∨
      Nonempty (S ≃* NativeSporadic.Co2) ∨ Nonempty (S ≃* NativeSporadic.Co3) ∨
      Nonempty (S ≃* NativeSporadic.HS) ∨ Nonempty (S ≃* NativeSporadic.McL) ∨
      Nonempty (S ≃* NativeSporadic.HN) ∨ Nonempty (S ≃* NativeSporadic.Suz) ∨
      Nonempty (S ≃* NativeSporadic.Ly) ∨ Nonempty (S ≃* NativeSporadic.Th) ∨
      Nonempty (S ≃* NativeSporadic.ON)) :
    ∃ z y : S, orderOf z = 2 ∧ orderOf y = 5 ∧ z * y = y * z ∧
      y ∈ Subgroup.centralizer (Subgroup.zpowers z : Set S) ∧
      Subgroup.centralizer (Subgroup.zpowers z : Set S) ≤
        Subgroup.normalizer (Subgroup.zpowers z : Set S) ∧
      y ∈ Subgroup.normalizer (Subgroup.zpowers z : Set S) := by
  have key : ∃ z y : S, orderOf z = 2 ∧ orderOf y = 5 ∧ z * y = y * z := by
    rcases hS with h | h | h | h | h | h | h | h | h | h | h <;> obtain ⟨e⟩ := h
    · exact exists_commuting_two_five_of_mulEquiv (G := NativeSporadic.J3) e
        j3_commuting_two_five
    · exact exists_commuting_two_five_of_mulEquiv (G := NativeSporadic.Co1) e
        co1_commuting_two_five
    · exact exists_commuting_two_five_of_mulEquiv (G := NativeSporadic.Co2) e
        co2_commuting_two_five
    · exact exists_commuting_two_five_of_mulEquiv (G := NativeSporadic.Co3) e
        co3_commuting_two_five
    · exact exists_commuting_two_five_of_mulEquiv (G := NativeSporadic.HS) e
        hs_commuting_two_five
    · exact exists_commuting_two_five_of_mulEquiv (G := NativeSporadic.McL) e
        mcl_commuting_two_five
    · exact exists_commuting_two_five_of_mulEquiv (G := NativeSporadic.HN) e
        hn_commuting_two_five
    · exact exists_commuting_two_five_of_mulEquiv (G := NativeSporadic.Suz) e
        suz_commuting_two_five
    · exact exists_commuting_two_five_of_mulEquiv (G := NativeSporadic.Ly) e
        ly_commuting_two_five
    · exact exists_commuting_two_five_of_mulEquiv (G := NativeSporadic.Th) e
        th_commuting_two_five
    · exact exists_commuting_two_five_of_mulEquiv (G := NativeSporadic.ON) e
        on_commuting_two_five
  obtain ⟨z, y, hz, hy, hzy⟩ := key
  have hC := mem_centralizer_zpowers_of_commute hzy
  exact ⟨z, y, hz, hy, hzy, hC, Subgroup.centralizer_le_normalizer _,
    Subgroup.centralizer_le_normalizer _ hC⟩

end CFSG.RankThree.Native
