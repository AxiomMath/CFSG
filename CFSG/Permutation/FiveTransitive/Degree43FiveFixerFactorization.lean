module

public import CFSG.Permutation.FiveTransitive.Degree43ThreeFree
public import CFSG.Permutation.FiveTransitive.Degree43FiveFixerArithmetic
public import CFSG.Permutation.FiveTransitive.Degree43SylowFiveOrder
public import CFSG.Permutation.FiveTransitive.Degree43LargePrimeFree
public import CFSG.Permutation.FiveTransitive.HighDegreeHallReduction

public section

namespace CFSG

namespace FiveTransitive.Degree43FiveFixerFactorization

open MulAction

private theorem two_pow_dvd_bound
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 43)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (a : ℕ)
    (ha : 2 ^ a ∣ Nat.card (fixingSubgroup P s)) : a ≤ 17 := by
  have hfix : 5 ≤ Nat.card (fixedPoints (fixingSubgroup P s) X) := by
    rw [Nat.card_coe_set_eq,← hs]
    exact Set.ncard_le_ncard (by
      intro x hx q
      exact (mem_fixingSubgroup_iff P).mp q.property x hx)
  have hd := Degree43FiveGroupBound.card_dvd_exterior_tuples
    P hcard h5 hnotAlt (fixingSubgroup P s) 5 17 (by norm_num) hfix
  by_contra hn
  have hb : 2 ^ 18 ∣ Nat.card (fixingSubgroup P s) :=
    (pow_dvd_pow 2 (by omega : 18 ≤ a)).trans ha
  have hc := hb.trans hd
  norm_num [Nat.descFactorial] at hc

private theorem card_exponents_of_three_free
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 43)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hthree : ¬ 3 ∣ Nat.card (fixingSubgroup P s)) :
    ∃ a b c : ℕ, 1 ≤ a ∧ a ≤ 17 ∧ b ≤ 1 ∧ c ≤ 1 ∧
      Nat.card (fixingSubgroup P s) = 2 ^ a * 5 ^ b * 7 ^ c ∧
      Nat.card P = 115511760 * 2 ^ a * 5 ^ b * 7 ^ c := by
  let _ := h5
  have hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card (fixingSubgroup P s) →
      p = 2 ∨ p = 5 ∨ p = 7 := by
    intro p hp hd
    have hlt : p < 11 := by
      by_contra hn
      exact Degree43LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs p hp (by omega) hd
    have hp3 : p ≠ 3 := by intro he; subst p; exact hthree hd
    interval_cases p <;> norm_num at *
  obtain ⟨a,ha,b,hb,c,hc,hH⟩ := Degree43FiveFixerArithmetic.factor_exponents Nat.card_pos.ne'
    (two_pow_dvd_bound P hcard h5 hnotAlt s hs)
    (Degree43SylowFiveOrder.twenty_five_not_dvd_five_fixer_card P hcard h5 hnotAlt s hs)
    (Degree43SevenOrder.forty_nine_not_dvd P hcard h5 hnotAlt s hs) hprimes
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
  refine ⟨a,b,c,ha0,ha,hb,hc,hH,?_⟩
  rw [← hm]
  ring

theorem card_exponents
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 43)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ∃ a b c : ℕ, 1 ≤ a ∧ a ≤ 17 ∧ b ≤ 1 ∧ c ≤ 1 ∧
      Nat.card (fixingSubgroup P s) = 2 ^ a * 5 ^ b * 7 ^ c ∧
      Nat.card P = 115511760 * 2 ^ a * 5 ^ b * 7 ^ c := by
  exact card_exponents_of_three_free P hcard h5 hnotAlt s hs
    (Degree43ThreeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs)

end FiveTransitive.Degree43FiveFixerFactorization

end CFSG
