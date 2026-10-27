module

public import CFSG.Permutation.FiveTransitive.Degree39FiveFixerFactorization
public import CFSG.Permutation.FiveTransitive.Degree39LargePrimeConstraints
public import CFSG.Permutation.FiveTransitive.Degree39ThirtySevenNormalizer
public import CFSG.Permutation.FiveTransitive.Degree39FiveFixerNumeric
public import CFSG.Permutation.FiveTransitive.HighDegreeHallReduction

public section

namespace CFSG

namespace FiveTransitive.Degree39FiveFixerOrder
open MulAction Degree39FiveFixerNumeric

theorem card_eq
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) = 1536 ∧ Nat.card P = 69090840 * 1536 := by
  let _ := h5
  obtain ⟨a,ha,b,hb,hH⟩ := Degree39FiveFixerFactorization.card_exponents P hcard h5 hnotAlt s hs
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
  have hP : Nat.card P = 69090840 * 2^a * 3^b := by rw [← hm]; ring
  obtain ⟨d19,k19,hd19,hk19,heq19⟩ :=
    Degree39LargePrimeConstraints.constraints P hcard h5 hnotAlt (Or.inl rfl)
  obtain ⟨d13,k13,hd13,hk13,heq13⟩ :=
    Degree39LargePrimeConstraints.constraints P hcard h5 hnotAlt (Or.inr rfl)
  obtain ⟨d37,k37,hd37,h2,hk37,heq37⟩ :=
    Degree39ThirtySevenNormalizer.constraints P hcard h5 hnotAlt
  norm_num at hd19 hd13
  have e19 := nineteen_residue hd19 hk19 (heq19.trans hP)
  have e13 := thirteen_residue hd13 hk13 (heq13.trans hP)
  have e37 := thirtyseven_residue hd37 h2 hk37 (heq37.trans hP)
  obtain ⟨rfl,rfl⟩ := exponents_eq ha0 ha hb e19 e13 e37
  constructor
  · simpa using hH
  · simpa using hP

end FiveTransitive.Degree39FiveFixerOrder

end CFSG
