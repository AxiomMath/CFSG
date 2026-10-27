module

public import CFSG.Permutation.FiveTransitive.Degree69LargePrimeSmallFree
public import CFSG.Permutation.FiveTransitive.Degree69NineteenFree
public import CFSG.Permutation.FiveTransitive.Degree69LargePrimeLong

public section

namespace CFSG

namespace FiveTransitive.Degree69LargePrimeFreeCore
open MulAction

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hseven : ¬ 7 ∣ Nat.card P) (s : Set X) (hs : s.ncard = 5)
    (p : ℕ) (hp : p.Prime) (hlarge : 11 ≤ p) : ¬ p ∣ Nat.card (fixingSubgroup P s) := by
  classical
  by_cases hsmall : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 23 ∨ p = 29 ∨ p = 31
  · exact Degree69LargePrimeSmallFree.small_not_dvd_five_fixer p hp hsmall P hcard h5 hnotAlt hseven s hs
  by_cases h19 : p = 19
  · subst p
    exact Degree69NineteenFree.not_dvd_five_fixer P hcard h5 hnotAlt hseven s hs
  have h33 : 33 ≤ p := by
    by_contra hn
    have hu : p ≤ 32 := by omega
    interval_cases p <;> norm_num at *
  let sf := s.toFinite.toFinset
  have he : (sf : Set X) = s := s.toFinite.coe_toFinset
  have hsf : sf.card = 5 := by rw [← Set.ncard_coe_finset,he]; exact hs
  have hh := Degree69LargePrimeLong.long_not_dvd_five_fixer P hcard h5 hnotAlt sf hsf p hp h33
  rwa [he] at hh

end FiveTransitive.Degree69LargePrimeFreeCore

end CFSG
