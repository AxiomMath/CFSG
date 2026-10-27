module

public import CFSG.Permutation.FiveTransitive.Degree67FiveFixerFactorization
public import CFSG.Permutation.FiveTransitive.Degree67SixtySevenNormalizer
public import CFSG.Permutation.FiveTransitive.Degree67SixtySevenNumeric

public section

namespace CFSG

namespace FiveTransitive.Degree67FiveFixerWindow

open MulAction

theorem exponent_cases_of_five_free
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hfive : ¬ 5 ∣ Nat.card (fixingSubgroup P s)) :
    ∃ a : ℕ, (a = 17 ∨ a = 18 ∨ a = 24 ∨ a = 25) ∧
      Nat.card (fixingSubgroup P s) = 2 ^ a ∧ Nat.card P = 1158917760 * 2 ^ a := by
  obtain ⟨a,ha0,ha,hH,hP⟩ := Degree67FiveFixerFactorization.order_of_five_free
    P hcard h5 hnotAlt s hs hfive
  obtain ⟨d,k,hd,hk,he⟩ := Degree67SixtySevenNormalizer.constraints P hcard h5 hnotAlt
  rw [hP] at he
  exact ⟨a,Degree67SixtySevenNumeric.exponent_cases ha0 ha
    (Degree67SixtySevenNumeric.residue hd hk he),hH,hP⟩

end FiveTransitive.Degree67FiveFixerWindow

end CFSG
