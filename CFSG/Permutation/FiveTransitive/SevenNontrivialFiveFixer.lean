module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Fintype.CardEmbedding

public section

namespace CFSG

namespace FiveTransitive.SevenNontrivialFiveFixer

open MulAction

theorem eq_top
    {X : Type*} [Fintype X] (J : Subgroup (Equiv.Perm X))
    (h7 : Nat.card X = 7) (h5 : IsMultiplyPretransitive J X 5)
    (b : Fin 5 ↪ X) (S : Sylow 2 (stabilizer J b))
    (hS : (S : Subgroup (stabilizer J b)) ≠ ⊥) :
    J = ⊤ ∧ Nat.card J = 5040 := by
  have hi := @index_stabilizer_of_transitive J (Fin 5 ↪ X) _ _ b h5
  rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin,
    ←Nat.card_eq_fintype_card, h7] at hi
  norm_num [Nat.descFactorial_succ] at hi
  have hc := (stabilizer J b).index_mul_card
  rw [hi] at hc
  have hn : Nontrivial S := (S : Subgroup (stabilizer J b)).nontrivial_iff_ne_bot.mpr hS
  have htwo := Finite.one_lt_card_iff_nontrivial.mpr hn
  have hSK : Nat.card S ≤ Nat.card (stabilizer J b) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hJ : Nat.card J ≤ 5040 := by
    have hh : Nat.card J ≤ Nat.card (Equiv.Perm X) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    simpa only [Nat.card_perm, h7, show Nat.factorial 7 = 5040 by norm_num [Nat.factorial]] using hh
  have hj : Nat.card J = 5040 := by omega
  refine ⟨Subgroup.eq_top_of_card_eq J ?_, hj⟩
  rw [Nat.card_perm, h7, hj]
  norm_num [Nat.factorial]

end FiveTransitive.SevenNontrivialFiveFixer

end CFSG
