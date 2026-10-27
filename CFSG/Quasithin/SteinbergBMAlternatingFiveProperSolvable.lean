module

public import CFSG.GroupTheory.OrderBelowSixtySolvable

public section

namespace CFSG.Quasithin.SteinbergBM

theorem alternating_five_proper_subgroup_solvable {α : Type*} [Fintype α] [DecidableEq α]
    (hα : Fintype.card α = 5) {H : Subgroup (alternatingGroup α)} (hH : H < ⊤) :
    Group.IsSolvable H := by
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hA : Nat.card (alternatingGroup α) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, hα]
    rfl
  apply CFSG.GroupTheory.groups_order_below_sixty_solvable
  rw [← hA]
  exact lt_of_le_of_ne (Subgroup.card_le_card_group H)
    fun h => hH.ne ((Subgroup.card_eq_iff_eq_top H).mp h)

end CFSG.Quasithin.SteinbergBM
