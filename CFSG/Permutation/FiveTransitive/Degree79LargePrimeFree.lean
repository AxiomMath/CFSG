module

public import CFSG.Permutation.FiveTransitive.Degree79LargePrimeSmallFree
public import CFSG.Permutation.FiveTransitive.Degree79LargePrimeLong

public section

namespace CFSG

namespace FiveTransitive.Degree79LargePrimeFree
open MulAction

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (p : ℕ) (hp : p.Prime) (hlarge : 11 ≤ p) :
    ¬ p ∣ Nat.card (fixingSubgroup P s) := by
  classical
  by_cases hc : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨ p = 31 ∨ p = 37
  · exact Degree79LargePrimeSmallFree.not_dvd_five_fixer p hp hc P hcard h5 hnotAlt s hs
  have hlong : 41 ≤ p := by
    by_contra hn
    have hu : p ≤ 40 := by omega
    interval_cases p <;> norm_num at *
  let sf := s.toFinite.toFinset
  have he : (sf : Set X) = s := s.toFinite.coe_toFinset
  have hsf : sf.card = 5 := by rw [← Set.ncard_coe_finset,he]; exact hs
  have ht := Degree79LargePrimeLong.long_not_dvd_five_fixer P hcard h5 hnotAlt sf hsf p hp hlong
  rwa [he] at ht

end FiveTransitive.Degree79LargePrimeFree

end CFSG
