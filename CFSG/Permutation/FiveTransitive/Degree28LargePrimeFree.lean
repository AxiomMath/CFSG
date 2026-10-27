module

public import CFSG.Permutation.FiveTransitive.Degree28LargePrimeThirteen
public import CFSG.Permutation.FiveTransitive.Degree28LargePrimeEleven

public section

namespace CFSG

namespace FiveTransitive.Degree28LargePrimeFree

open MulAction

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Finset X) (hs : s.card = 5) (p : ℕ) (hp : p.Prime) (hlarge : 11 ≤ p) :
    ¬ p ∣ Nat.card (fixingSubgroup P (s : Set X)) := by
  by_cases h11 : p = 11
  · subst p
    exact Degree28LargePrimeEleven.not_dvd_five_fixer P hcard h5 hnotAlt s hs
  · have h13 : 13 ≤ p := by
      have h12 : p ≠ 12 := by intro he; rw [he] at hp; norm_num at hp
      omega
    exact Degree28LargePrimeThirteen.not_dvd_five_fixer P hcard h5 hnotAlt s hs p hp h13

end FiveTransitive.Degree28LargePrimeFree

end CFSG
