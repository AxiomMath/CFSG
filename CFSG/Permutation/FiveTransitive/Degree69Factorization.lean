module

public import CFSG.Permutation.FiveTransitive.Degree69FactorizationArithmetic
public import CFSG.Permutation.FiveTransitive.Degree69FiveFree
public import CFSG.Permutation.FiveTransitive.Degree69LargePrimeFree
public import CFSG.Permutation.FiveTransitive.HighDegreeHallReduction

public section

namespace CFSG

namespace FiveTransitive.Degree69Factorization

open MulAction

theorem card_exponents
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ∃ a b : ℕ, 1 ≤ a ∧
      Nat.card (fixingSubgroup P s) = 2 ^ a * 3 ^ b ∧
      Nat.card P = 1348621560 * 2 ^ a * 3 ^ b := by
  let _ := h5
  have hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card (fixingSubgroup P s) →
      p = 2 ∨ p = 3 := by
    intro p hp hd
    have hlt : p < 11 := by
      by_contra hn
      exact Degree69LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs p hp (by omega) hd
    have hp5 : p ≠ 5 := by
      intro he; subst p
      exact Degree69FiveFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs hd
    have hp7 : p ≠ 7 := by
      intro he; subst p
      exact Degree69SevenFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs hd
    interval_cases p <;> norm_num at *
  obtain ⟨a,b,hH⟩ := Degree69FactorizationArithmetic.factor_exponents Nat.card_pos.ne' hprimes
  have heven := Research.HighDegreeHallReduction.even_card_fixingSubgroup_of_five_transitive
    X P (by omega) h5 s hs
  have ha0 : 1 ≤ a := by
    by_contra hn
    have haeq : a = 0 := by omega
    have htwo := even_iff_two_dvd.mp heven
    rw [hH,haeq,pow_zero,one_mul] at htwo
    have hh := Nat.prime_two.dvd_of_dvd_pow htwo
    norm_num at hh
  have hi := IsMultiplyPretransitive.index_of_fixingSubgroup_eq (G := P) s (by rwa [hs])
  rw [Nat.card_eq_fintype_card,hcard,hs] at hi
  norm_num [Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial] at hi
  have hm := (fixingSubgroup P s).index_mul_card
  rw [hi,hH] at hm
  refine ⟨a,b,ha0,hH,?_⟩
  rw [← hm]
  ring

end FiveTransitive.Degree69Factorization

end CFSG
