module

public import CFSG.Permutation.FiveTransitive.Degree69TwoBound

public section

namespace CFSG

namespace FiveTransitive.Degree69TwoExponent
open MulAction

theorem two_exponent_le_six
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (a : ℕ)
    (ha : 2 ^ a ∣ Nat.card (fixingSubgroup P s)) : a ≤ 6 := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  let S : Sylow 2 (fixingSubgroup P s) := Sylow.nonempty.some
  have hdiv : 2 ^ a ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card ha
  have hle : 2 ^ a ≤ 64 := (Nat.le_of_dvd Nat.card_pos hdiv).trans
    (Degree69TwoBound.sylow_card_le_sixtyFour P hcard h5 hnotAlt s hs S)
  by_contra hn
  have hh : 2 ^ 7 ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) (by omega)
  norm_num at hh
  omega

end FiveTransitive.Degree69TwoExponent

end CFSG
