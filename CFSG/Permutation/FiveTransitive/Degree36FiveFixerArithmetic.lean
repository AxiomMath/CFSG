module

public import CFSG.Permutation.FiveTransitive.Degree36FiveFixerNumeric
public import CFSG.Permutation.FiveTransitive.Degree36FiveFixerRefinedFactors
public import CFSG.Permutation.FiveTransitive.Degree36LargeSylowNormalizer
public import CFSG.Permutation.FiveTransitive.HighDegreeHallReduction

public section

namespace CFSG

namespace FiveTransitive.Degree36FiveFixerArithmetic

open MulAction Degree36FiveFixerNumeric

private theorem card_and_exponents
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ∃ a, 1 ≤ a ∧ a ≤ 11 ∧ ∃ b ≤ 8, ∃ c ≤ 1,
      Nat.card (fixingSubgroup P s) = 2^a * 3^b * 5^c ∧
      Nat.card P = 45239040 * 2^a * 3^b * 5^c := by
  let _ := h5
  obtain ⟨a,ha,b,hb,c,hc,hH⟩ :=
    Degree36FiveFixerRefinedFactors.card_exponents P hcard h5 hnotAlt s hs
  have heven := Research.HighDegreeHallReduction.even_card_fixingSubgroup_of_five_transitive
    X P (by omega) h5 s hs
  have ha0 : 1 ≤ a := by
    by_contra hn
    have haeq : a = 0 := by omega
    have htwo := even_iff_two_dvd.mp heven
    rw [hH,haeq,pow_zero,one_mul] at htwo
    rcases Nat.prime_two.dvd_mul.mp htwo with h | h
    · have hh := Nat.prime_two.dvd_of_dvd_pow h
      norm_num at hh
    · have hh := Nat.prime_two.dvd_of_dvd_pow h
      norm_num at hh
  have hi := IsMultiplyPretransitive.index_of_fixingSubgroup_eq (G := P) s (by rwa [hs])
  rw [Nat.card_eq_fintype_card,hcard,hs] at hi
  norm_num [Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial] at hi
  have hm := (fixingSubgroup P s).index_mul_card
  rw [hi,hH] at hm
  exact ⟨a,ha0,ha,b,hb,c,hc,hH,by rw [← hm]; ring⟩

theorem card_exponents_mem
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ∃ a b c : ℕ, (a,b,c) ∈ allowedTriples ∧
      Nat.card (fixingSubgroup P s) = 2^a * 3^b * 5^c ∧
      Nat.card P = 45239040 * 2^a * 3^b * 5^c := by
  obtain ⟨a,ha0,ha,b,hb,c,hc,hH,hP⟩ := card_and_exponents P hcard h5 hnotAlt s hs
  obtain ⟨d17,k17,hd17,he17,hk17,heq17,_⟩ :=
    Degree36LargeSylowNormalizer.combined_constraints P hcard h5 hnotAlt (Or.inl rfl)
  obtain ⟨d11,k11,hd11,he11,hk11,heq11,hthree⟩ :=
    Degree36LargeSylowNormalizer.combined_constraints P hcard h5 hnotAlt (Or.inr rfl)
  norm_num at hd17 hd11
  have hsix : 6 ∣ d11 := (show Nat.Coprime 2 3 by norm_num).mul_dvd_of_dvd_of_dvd he11
    (hthree rfl)
  refine ⟨a,b,c,?_,hH,hP⟩
  exact exponents_mem ha0 ha hb hc hd17 he17 hk17 (by rwa [← hP])
    hd11 hsix hk11 (by rwa [← hP])

end FiveTransitive.Degree36FiveFixerArithmetic

end CFSG
