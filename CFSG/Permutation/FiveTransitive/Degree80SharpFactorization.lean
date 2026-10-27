module

public import CFSG.Permutation.FiveTransitive.Degree80OddFactorizationBounds
public import CFSG.Permutation.FiveTransitive.Degree80FactorizationArithmetic
public import CFSG.Permutation.FiveTransitive.Degree80FactorizationBounds
public import CFSG.Permutation.FiveTransitive.Degree80LargePrimeFree

public section

namespace CFSG

namespace FiveTransitive.Degree80SharpFactorization
open MulAction

theorem card_exponents
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ∃ a b c : ℕ, 1 ≤ a ∧ a ≤ 36 ∧ b ≤ 1 ∧ c ≤ 2 ∧
      Nat.card (fixingSubgroup P s) = 2 ^ a * 3 ^ b * 5 ^ c ∧
      Nat.card P = 2884801920 * 2 ^ a * 3 ^ b * 5 ^ c := by
  let _ := h5
  have hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card (fixingSubgroup P s) →
      p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    intro p hp hd
    have hlt : p < 11 := by
      by_contra hn
      exact Degree80LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs p hp (by omega) hd
    interval_cases p <;> norm_num at *
  let h := Nat.card (fixingSubgroup P s)
  have hH := Degree80FactorizationArithmetic.factor_exponents (h := h) Nat.card_pos.ne' hprimes
  have hseven : h.factorization 7 = 0 := Nat.factorization_eq_zero_of_not_dvd
    (Degree80SevenFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs)
  rw [hseven,pow_zero,mul_one] at hH
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
  refine ⟨h.factorization 2,h.factorization 3,h.factorization 5,ha0,
    Degree80FactorizationBounds.two_le P hcard h5 hnotAlt s hs,
    Degree80OddFactorizationBounds.three_le P hcard h5 hnotAlt s hs,
    Degree80OddFactorizationBounds.five_le P hcard h5 hnotAlt s hs,
    hH,?_⟩
  rw [← hm]
  ring

end FiveTransitive.Degree80SharpFactorization

end CFSG
