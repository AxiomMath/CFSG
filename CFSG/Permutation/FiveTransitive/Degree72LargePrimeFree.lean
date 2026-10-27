module

public import CFSG.Permutation.FiveTransitive.Degree72LargePrimeSmallFree
public import CFSG.Permutation.FiveTransitive.Degree72LargePrimeLong

public section

namespace CFSG

namespace FiveTransitive.Degree72LargePrimeFree
open MulAction

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (p : ℕ) (hp : p.Prime) (hlarge : 13 ≤ p) :
    ¬ p ∣ Nat.card (fixingSubgroup P s) := by
  classical
  by_cases hc : p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨ p = 31
  · exact Degree72LargePrimeSmallFree.not_dvd_five_fixer p hp hc P hcard h5 hnotAlt s hs
  have hlong : 37 ≤ p := by
    by_contra hn
    have hu : p ≤ 36 := by omega
    interval_cases p <;> norm_num at *
  let sf := s.toFinite.toFinset
  have he : (sf : Set X) = s := s.toFinite.coe_toFinset
  have hsf : sf.card = 5 := by rw [← Set.ncard_coe_finset,he]; exact hs
  have ht := Degree72LargePrimeLong.long_not_dvd_five_fixer P hcard h5 hnotAlt sf hsf p hp hlong
  rwa [he] at ht

end FiveTransitive.Degree72LargePrimeFree

end CFSG
