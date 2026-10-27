module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec14

namespace Res9ON

theorem card_alternatingGroup_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  have hcard := (alternatingGroup (Fin 7)).card_mul_index
  have h7 : Nat.card (Equiv.Perm (Fin 7)) = 5040 := by
    rw [Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.factorial]
  rw [alternatingGroup.index_eq_two, h7] at hcard
  omega

theorem card_of_isTripleCover_a7 {X : Type*} [Group X]
    (h : Sec4.IsTripleCover X (alternatingGroup (Fin 7))) : Nat.card X = 7560 := by
  obtain ⟨h3, ⟨ψ⟩⟩ := h
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
  rw [Nat.card_congr ψ.toEquiv, card_alternatingGroup_seven, h3] at hc
  omega

end Res9ON

end CFSG.RankThree.PartTwo.Sec14
