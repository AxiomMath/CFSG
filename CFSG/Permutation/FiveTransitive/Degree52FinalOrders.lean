module

public import CFSG.Permutation.FiveTransitive.Degree52FourOrders
public import CFSG.Permutation.FiveTransitive.Degree52SeventeenTransfer

public section

namespace CFSG

namespace FiveTransitive.Degree52FinalOrders
open MulAction

private theorem five_fixer_card_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) = 32 ∨ Nat.card (fixingSubgroup P s) = 96 := by
  have hn := Degree52SeventeenTransfer.excluded_five_fixer_orders P hcard h5 hnotAlt s hs
  rcases Degree52FourOrders.five_fixer_card_cases P hcard h5 hnotAlt s hs with h | h | h | h
  · exact (hn (Or.inl h)).elim
  · exact Or.inl h
  · exact (hn (Or.inr h)).elim
  · exact Or.inr h

theorem sylow_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s)) :
    Nat.card S = 32 := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  rcases Degree52TwoOrder.card_sixteen_or_thirtyTwo P hcard h5 hnotAlt s hs S with hS | hS
  · have hH := five_fixer_card_cases P hcard h5 hnotAlt s hs
    have hm := (S : Subgroup (fixingSubgroup P s)).card_mul_index
    rw [hS] at hm
    have hn := S.not_dvd_index
    omega
  · exact hS

end FiveTransitive.Degree52FinalOrders

end CFSG
