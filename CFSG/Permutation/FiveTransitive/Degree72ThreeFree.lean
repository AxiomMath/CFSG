module

public import CFSG.Permutation.FiveTransitive.Degree72ThreeConditionalFree
public import CFSG.Permutation.FiveTransitive.Degree72ElevenGlobal

public section

namespace CFSG

namespace FiveTransitive.Degree72ThreeFree
open MulAction

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 3 ∣ Nat.card (fixingSubgroup P s) := by
  apply Degree72ThreeConditionalFree.not_dvd_five_fixer P hcard h5 hnotAlt _ s hs
  intro g hg
  rw [Degree72ElevenGlobal.fixed_card_eq_six P hcard h5 hnotAlt g hg]
  decide

end FiveTransitive.Degree72ThreeFree

end CFSG
