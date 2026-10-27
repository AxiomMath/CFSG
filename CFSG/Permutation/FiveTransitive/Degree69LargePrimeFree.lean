module

public import CFSG.Permutation.FiveTransitive.Degree69LargePrimeFreeCore
public import CFSG.Permutation.FiveTransitive.Degree69SevenFree

public section

namespace CFSG

namespace FiveTransitive.Degree69LargePrimeFree
open MulAction

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (p : ℕ) (hp : p.Prime) (hlarge : 11 ≤ p) :
    ¬ p ∣ Nat.card (fixingSubgroup P s) := by
  exact Degree69LargePrimeFreeCore.not_dvd_five_fixer P hcard h5 hnotAlt
    (Degree69SevenFree.not_dvd_ambient P hcard h5 hnotAlt) s hs p hp hlarge

end FiveTransitive.Degree69LargePrimeFree

end CFSG
