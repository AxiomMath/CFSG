module

public import CFSG.Permutation.FiveTransitive.Degree72Factorization
public import CFSG.Permutation.FiveTransitive.Degree72FiveFree

public section

namespace CFSG

namespace FiveTransitive.Degree72PureTwo
open MulAction

theorem card_exponent
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ 64 ∧ Nat.card (fixingSubgroup P s) = 2 ^ a ∧
      Nat.card P = 1678985280 * 2 ^ a := by
  obtain ⟨a,c,d,ha0,ha,hc,hd,hH,hP⟩ := Degree72Factorization.card_exponents P hcard h5 hnotAlt s hs
  have hc0 : c = 0 := by
    by_contra hn
    have hc1 : c = 1 := by omega
    have hfree := Degree72FiveFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs
    apply hfree
    rw [hH,hc1,pow_one]
    exact dvd_mul_of_dvd_left (dvd_mul_left 5 (2 ^ a)) _
  have hd0 : d = 0 := by
    by_contra hn
    have hd1 : d = 1 := by omega
    have hfree := Degree72ElevenFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs
    apply hfree
    rw [hH,hd1,pow_one]
    exact dvd_mul_left _ _
  simp only [hc0,hd0,pow_zero,mul_one] at hH hP
  exact ⟨a,ha0,ha,hH,hP⟩

end FiveTransitive.Degree72PureTwo

end CFSG
