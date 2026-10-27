module

public import CFSG.Permutation.FiveTransitive.Degree72FactorizationBounds
public import CFSG.Permutation.FiveTransitive.Degree72ThreeFree
public import CFSG.Permutation.FiveTransitive.Degree72LargePrimeFree

public section

namespace CFSG

namespace FiveTransitive.Degree72Factorization
open MulAction

theorem card_exponents
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ∃ a c d : ℕ, 1 ≤ a ∧ a ≤ 64 ∧ c ≤ 1 ∧ d ≤ 1 ∧
      Nat.card (fixingSubgroup P s) = 2 ^ a * 5 ^ c * 11 ^ d ∧
      Nat.card P = 1678985280 * 2 ^ a * 5 ^ c * 11 ^ d := by
  let _ := h5
  have hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card (fixingSubgroup P s) →
      p = 2 ∨ p = 5 ∨ p = 11 := by
    intro p hp hd
    have hlt : p < 13 := by
      by_contra hn
      exact Degree72LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs p hp (by omega) hd
    have hp3 : p ≠ 3 := by
      intro he; subst p
      exact Degree72ThreeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs hd
    have hp7 : p ≠ 7 := by
      intro he; subst p
      exact Degree72FiveSevenFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs hd
    interval_cases p <;> norm_num at *
  let h := Nat.card (fixingSubgroup P s)
  have hH := Degree72FactorizationArithmetic.factor_exponents (h := h) Nat.card_pos.ne' hprimes
  have heven := Research.HighDegreeHallReduction.even_card_fixingSubgroup_of_five_transitive
    X P (by omega) h5 s hs
  have ha0 : 1 ≤ h.factorization 2 := Nat.prime_two.factorization_pos_of_dvd Nat.card_pos.ne'
    (even_iff_two_dvd.mp heven)
  have hi := IsMultiplyPretransitive.index_of_fixingSubgroup_eq (G := P) s (by rwa [hs])
  rw [Nat.card_eq_fintype_card,hcard,hs] at hi
  norm_num [Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial] at hi
  have hm := (fixingSubgroup P s).index_mul_card
  change _ * h = _ at hm
  rw [hi,hH] at hm
  refine ⟨h.factorization 2,h.factorization 5,h.factorization 11,ha0,
    Degree72FactorizationBounds.two_le P hcard s hs,
    Degree72FactorizationBounds.five_le P hcard h5 hnotAlt s hs,
    Degree72FactorizationBounds.eleven_le P hcard h5 hnotAlt s hs,hH,?_⟩
  rw [← hm]
  ring

end FiveTransitive.Degree72Factorization

end CFSG
