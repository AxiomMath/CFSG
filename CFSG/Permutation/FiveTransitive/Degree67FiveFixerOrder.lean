module

public import CFSG.Permutation.FiveTransitive.Degree67FiveFixerWindow
public import CFSG.Permutation.FiveTransitive.Degree67FiveFree

public section

namespace CFSG

namespace FiveTransitive.Degree67FiveFixerOrder

open MulAction

private theorem exponent_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ∃ a : ℕ, (a = 17 ∨ a = 18 ∨ a = 24 ∨ a = 25) ∧
      Nat.card (fixingSubgroup P s) = 2 ^ a ∧ Nat.card P = 1158917760 * 2 ^ a := by
  exact Degree67FiveFixerWindow.exponent_cases_of_five_free P hcard h5 hnotAlt s hs
    (Degree67FiveFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs)

theorem two_pow_seventeen_dvd
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    2 ^ 17 ∣ Nat.card (fixingSubgroup P s) := by
  obtain ⟨a,ha,hH,_⟩ := exponent_cases P hcard h5 hnotAlt s hs
  rw [hH]
  exact pow_dvd_pow 2 (by rcases ha with rfl | rfl | rfl | rfl <;> omega)

end FiveTransitive.Degree67FiveFixerOrder

end CFSG
