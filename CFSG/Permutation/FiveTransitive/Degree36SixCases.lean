module

public import CFSG.Permutation.FiveTransitive.Degree36SixCasesNumeric
public import CFSG.Permutation.FiveTransitive.Degree36FifteenCases
public import CFSG.Permutation.FiveTransitive.Degree36SmallThreeOrder
public import CFSG.Permutation.FiveTransitive.Degree36FiveThreeExclusion

public section

namespace CFSG

namespace FiveTransitive.Degree36SixCases

open MulAction

private theorem sylow_three_card_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 3 (fixingSubgroup P s)) :
    Nat.card S = 1 ∨ Nat.card S = 3 ∨ Nat.card S = 81 := by
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  by_cases hS : Nat.card S = 1
  · exact Or.inl hS
  have hbound := Degree36SylowThreeSharp.card_le_eighty_one P hcard h5 hnotAlt s hs S
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have he4 : e ≤ 4 := by
    by_contra hn
    have hp := Nat.pow_le_pow_right (by norm_num : 0 < 3) (by omega : 5 ≤ e)
    rw [← he] at hp
    norm_num at hp
    omega
  by_cases he3 : e ≤ 3
  · apply Or.inr ∘ Or.inl
    apply Degree36SmallThreeOrder.card_eq_three P hcard h5 hnotAlt s hs S hS
    rw [he]
    exact Nat.pow_le_pow_right (by norm_num : 0 < 3) he3
  · have heq : e = 4 := by omega
    exact Or.inr (Or.inr (by rw [he,heq]; norm_num))

theorem card_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) = 2 ∨ Nat.card (fixingSubgroup P s) = 4 ∨
      Nat.card (fixingSubgroup P s) = 128 ∨ Nat.card (fixingSubgroup P s) = 256 ∨
      Nat.card (fixingSubgroup P s) = 41472 ∨ Nat.card (fixingSubgroup P s) = 82944 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨a,b,c,hm,hH,_⟩ := Degree36FifteenCases.card_exponents_mem P hcard h5 hnotAlt s hs
  let S : Sylow 3 (fixingSubgroup P s) := Sylow.nonempty.some
  have hScases := sylow_three_card_cases P hcard h5 hnotAlt s hs S
  rw [S.card_eq_multiplicity,hH,Degree36SixCasesNumeric.three_factorization] at hScases
  have hfree : ¬ 9 ∣ 2^a * 3^b * 5^c → ¬ 5 ∣ 2^a * 3^b * 5^c := by
    rw [← hH]
    exact Degree36FiveThreeExclusion.five_not_dvd_of_nine_not_dvd P hcard h5 hnotAlt s hs
  rw [hH]
  exact Degree36SixCasesNumeric.six_values hm hScases hfree

end FiveTransitive.Degree36SixCases

end CFSG
