module

public import CFSG.Permutation.FiveTransitive.Degree67TwoFiveOrder
public import CFSG.Permutation.FiveTransitive.Degree67TwoSevenExcluded

public section

namespace CFSG

namespace FiveTransitive.Degree67Classification
open MulAction

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) : alternatingGroup X ≤ P := by
  by_contra hnotAlt
  obtain ⟨s,_,hs⟩ := Set.exists_subset_card_eq
    (show 5 ≤ (Set.univ : Set X).ncard by simp [Set.ncard_univ,hcard])
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  let S : Sylow 2 (fixingSubgroup P s) := Classical.choice inferInstance
  have hF := Degree67TwoSevenExcluded.fixed_card_eq_five P hcard h5 hnotAlt s hs S
  have hup := Degree67TwoFiveOrder.card_le P hcard h5 hnotAlt s hs S hF
  have hd := S.pow_dvd_card_of_pow_dvd_card
    (Degree67FiveFixerOrder.two_pow_seventeen_dvd P hcard h5 hnotAlt s hs)
  have hlo := Nat.le_of_dvd (Nat.card_pos (α := S)) hd
  norm_num at hlo
  omega

end FiveTransitive.Degree67Classification

end CFSG
