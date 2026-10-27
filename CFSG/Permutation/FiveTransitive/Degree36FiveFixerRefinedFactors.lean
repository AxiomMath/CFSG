module

public import CFSG.Permutation.FiveTransitive.Degree36FiveFixerFactors
public import CFSG.Permutation.FiveTransitive.Degree36OrderFiveFixed

public section

namespace CFSG

namespace FiveTransitive.Degree36FiveFixerRefinedFactors

open MulAction

theorem card_exponents
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ∃ a ≤ 11, ∃ b ≤ 8, ∃ c ≤ 1,
      Nat.card (fixingSubgroup P s) = 2 ^ a * 3 ^ b * 5 ^ c := by
  obtain ⟨a,ha,b,hb,c,_,hc⟩ := Degree36FiveFixerFactors.card_exponents P hcard h5 hnotAlt s hs
  have hc1 : c ≤ 1 := by
    by_contra hn
    apply Degree36OrderFiveFixed.twenty_five_not_dvd_five_fixer_card P hcard h5 hnotAlt s hs
    rw [hc]
    exact (show 5^2 ∣ 5^c from pow_dvd_pow 5 (by omega)).trans (dvd_mul_left _ _)
  exact ⟨a,ha,b,hb,c,hc1,hc⟩

end FiveTransitive.Degree36FiveFixerRefinedFactors

end CFSG
