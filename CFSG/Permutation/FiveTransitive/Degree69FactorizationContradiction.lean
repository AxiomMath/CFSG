module

public import CFSG.Permutation.FiveTransitive.Degree69Factorization
public import CFSG.Permutation.FiveTransitive.Degree69FactorizationNumeric
public import CFSG.Permutation.FiveTransitive.Degree69SixtySevenNormalizer
public import CFSG.Permutation.FiveTransitive.Degree69TwentyThreeNormalizer

public section

namespace CFSG

namespace FiveTransitive.Degree69FactorizationContradiction
open MulAction

theorem excluded_of_power_bounds
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (htwo : ∀ a : ℕ, 2 ^ a ∣ Nat.card (fixingSubgroup P s) → a ≤ 6)
    (hthree : ∀ b : ℕ, 3 ^ b ∣ Nat.card (fixingSubgroup P s) → b ≤ 10) : False := by
  obtain ⟨a,b,ha0,hH,hP⟩ := Degree69Factorization.card_exponents P hcard h5 hnotAlt s hs
  have ha : a ≤ 6 := htwo a (hH ▸ dvd_mul_right _ _)
  have hb : b ≤ 10 := hthree b (hH ▸ dvd_mul_left _ _)
  obtain ⟨d,k,hd,heven,hk,he⟩ := Degree69SixtySevenNormalizer.constraints P hcard h5 hnotAlt
  obtain ⟨c,j,hc,hj,hf⟩ := Degree69TwentyThreeNormalizer.actual_constraints P hcard h5 hnotAlt
  rw [hP] at he hf
  exact Degree69FactorizationNumeric.excluded ha0 ha hb
    (Degree69FactorizationNumeric.residue67 hd heven hk he)
    (Degree69FactorizationNumeric.residue23 hc hj hf)

end FiveTransitive.Degree69FactorizationContradiction

end CFSG
