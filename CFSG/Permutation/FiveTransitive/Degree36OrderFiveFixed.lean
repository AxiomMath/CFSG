module

public import CFSG.Permutation.FiveTransitive.Degree36OrderFiveFixedReduction
public import CFSG.Permutation.FiveTransitive.Degree36SylowFiveOrder

public section

namespace CFSG

namespace FiveTransitive.Degree36OrderFiveFixed

open MulAction

private theorem sylow_card_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 5 (fixingSubgroup P s)) :
    Nat.card S = 1 ∨ Nat.card S = 5 := by
  by_cases hS : Nat.card S = 1
  · exact Or.inl hS
  · exact Or.inr (Degree36SylowFiveOrder.card_eq_five P hcard h5 hnotAlt s hs S hS)

theorem fixed_card_eq_six
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 5) (hfixed : 5 ≤ Nat.card (Function.fixedPoints g.val)) :
    Nat.card (Function.fixedPoints g.val) = 6 :=
  Degree36OrderFiveFixedReduction.fixed_card_of_sylow_orders P hcard h5 hnotAlt
    (sylow_card_cases P hcard h5 hnotAlt) g hg hfixed

theorem twenty_five_not_dvd_five_fixer_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 25 ∣ Nat.card (fixingSubgroup P s) :=
  Degree36OrderFiveFixedReduction.twenty_five_not_dvd_of_sylow_orders P
    (sylow_card_cases P hcard h5 hnotAlt) s hs

end FiveTransitive.Degree36OrderFiveFixed

end CFSG
