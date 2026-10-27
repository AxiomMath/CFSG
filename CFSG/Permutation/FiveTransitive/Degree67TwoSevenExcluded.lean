module

public import CFSG.Permutation.FiveTransitive.Degree67TwoSevenOrder
public import CFSG.Permutation.FiveTransitive.Degree67FiveFixerOrder

public section

namespace CFSG

namespace FiveTransitive.Degree67TwoSevenExcluded
open MulAction SylowFixedActionCore

theorem fixed_card_eq_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s)) :
    Nat.card (sylowFixedPoints X P s S) = 5 := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  rcases Degree67TwoEntrance.fixed_card_cases P hcard h5 s hs S with hF | hF
  · exact hF
  · have hup := Degree67TwoSevenOrder.card_le P hcard h5 hnotAlt s hs S hF
    have hd := S.pow_dvd_card_of_pow_dvd_card
      (Degree67FiveFixerOrder.two_pow_seventeen_dvd P hcard h5 hnotAlt s hs)
    have hlo := Nat.le_of_dvd (Nat.card_pos (α := S)) hd
    norm_num at hlo
    omega

end FiveTransitive.Degree67TwoSevenExcluded

end CFSG
