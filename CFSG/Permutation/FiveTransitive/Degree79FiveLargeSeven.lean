module

public import CFSG.Permutation.FiveTransitive.Degree79FiveLargeSevenFromSupport
public import CFSG.Permutation.FiveTransitive.A9FourteenQuotientSupport

public section

namespace CFSG

namespace FiveTransitive.Degree79FiveLargeSeven
open MulAction SylowFixedActionCore A9PrimeFreeOrbitImage

theorem exists_normalizer_seven
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    ∃ g : sylowNormalizer X P s S, orderOf g = 7 ∧
      10 ≤ Nat.card (Function.fixedPoints g.val.val) := by
  exact Degree79FiveLargeSevenFromSupport.exists_normalizer_seven P hcard h5 hnotAlt
    (@A9FourteenQuotientSupport.support_le_seven) s hs S hS

end FiveTransitive.Degree79FiveLargeSeven

end CFSG
