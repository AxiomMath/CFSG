module

public import CFSG.Permutation.FiveTransitive.Degree67FiveFixerArithmetic
public import CFSG.Permutation.FiveTransitive.Degree67FiveFixerTupleBounds
public import CFSG.Permutation.FiveTransitive.Degree67ThreeFree
public import CFSG.Permutation.FiveTransitive.Degree67ElevenFree
public import CFSG.Permutation.FiveTransitive.Degree67LargePrimeFree

public section

namespace CFSG

namespace FiveTransitive.Degree67FiveFixerFactorization

open MulAction

theorem order_of_five_free
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hfive : ¬ 5 ∣ Nat.card (fixingSubgroup P s)) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ 26 ∧ Nat.card (fixingSubgroup P s) = 2 ^ a ∧
      Nat.card P = 1158917760 * 2 ^ a := by
  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card (fixingSubgroup P s) → p = 2 := by
    intro p hp hd
    have hlt : p < 13 := by
      by_contra hn
      exact Degree67LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs p hp (by omega) hd
    have hp3 : p ≠ 3 := by
      intro he; subst p
      exact Degree67ThreeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs hd
    have hp5 : p ≠ 5 := by intro he; subst p; exact hfive hd
    have hp7 : p ≠ 7 := by
      intro he; subst p
      exact Degree67SevenFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs hd
    have hp11 : p ≠ 11 := by
      intro he; subst p
      exact Degree67ElevenFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs hd
    interval_cases p <;> norm_num at *
  obtain ⟨a,ha,hH⟩ := Degree67FiveFixerArithmetic.factor_exponent Nat.card_pos.ne'
    (Degree67FiveFixerTupleBounds.two_pow_dvd_bound P hcard h5 hnotAlt s hs) hprime
  have ha0 : 1 ≤ a := by
    have heven := Research.HighDegreeHallReduction.even_card_fixingSubgroup_of_five_transitive
      X P (by omega) h5 s hs
    have hd := even_iff_two_dvd.mp heven
    by_contra hn
    have haeq : a = 0 := by omega
    rw [hH,haeq,pow_zero] at hd
    norm_num at hd
  have hi := IsMultiplyPretransitive.index_of_fixingSubgroup_eq (G := P) s (by rwa [hs])
  rw [Nat.card_eq_fintype_card,hcard,hs] at hi
  norm_num [Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial] at hi
  have hm := (fixingSubgroup P s).index_mul_card
  rw [hi,hH] at hm
  exact ⟨a,ha0,ha,hH,hm.symm⟩

end FiveTransitive.Degree67FiveFixerFactorization

end CFSG
