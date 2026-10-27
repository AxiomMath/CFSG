module

public import CFSG.Permutation.FiveTransitive.Degree60FiveFixerSmallWindow
public import CFSG.Permutation.FiveTransitive.Degree60ThreeBound
public import CFSG.Permutation.FiveTransitive.Degree60ElevenDescentOrder

public section

namespace CFSG

namespace FiveTransitive.Degree60Classification
open MulAction

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) : alternatingGroup X ≤ P := by
  by_contra hnotAlt
  obtain ⟨s,_,hs⟩ := Set.exists_subset_card_eq
    (show 5 ≤ (Set.univ : Set X).ncard by simp [Set.ncard_univ,hcard])
  exact Degree60FiveFixerSmallWindow.excluded_of_sylow_bounds P hcard h5 hnotAlt s hs
    (fun S => (Degree60ThreeBound.card_le_243 P hcard h5 hnotAlt s hs S).trans (by decide))
    (Degree60FiveOrder.sylow_card_le_five P hcard h5 hnotAlt s hs)
    (Degree60ElevenDescentOrder.sylow_card_le_eleven P hcard h5 hnotAlt s hs)

end FiveTransitive.Degree60Classification

end CFSG
