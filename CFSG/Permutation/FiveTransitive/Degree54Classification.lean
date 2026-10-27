module

public import CFSG.Permutation.FiveTransitive.Degree54FiveFixerSmallWindow
public import CFSG.Permutation.FiveTransitive.Degree54TwoOrderBound
public import CFSG.Permutation.FiveTransitive.Degree54ThreeNotTwentySeven

public section

namespace CFSG

namespace FiveTransitive.Degree54Classification
open MulAction

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) : alternatingGroup X ≤ P := by
  by_contra hnotAlt
  obtain ⟨s,_,hs⟩ := Set.exists_subset_card_eq
    (show 5 ≤ (Set.univ : Set X).ncard by simp [Set.ncard_univ,hcard])
  let S : Sylow 2 (fixingSubgroup P s) := Sylow.nonempty.some
  let T : Sylow 3 (fixingSubgroup P s) := Sylow.nonempty.some
  have hS := Degree54TwoOrderBound.sylow_card_le_five_twelve P hcard h5 hnotAlt s hs S
  have hT := (Degree54FiveFixerSmallWindow.sylow_orders_of_two_le
    P hcard h5 hnotAlt s hs S hS T).2
  exact Degree54ThreeNotTwentySeven.card_ne_twentySeven P hcard h5 hnotAlt s hs T hT

end FiveTransitive.Degree54Classification

end CFSG
