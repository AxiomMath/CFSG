module

public import CFSG.Permutation.FiveTransitive.Degree52ThreeSharpOrder
public import CFSG.Permutation.FiveTransitive.Degree52FiveFixerArithmetic
public import CFSG.Permutation.FiveTransitive.Degree52FiveFree
public import CFSG.Permutation.FiveTransitive.Degree52LargePrimeFree
public import CFSG.Permutation.FiveTransitive.HighDegreeHallReduction

public section

namespace CFSG

namespace FiveTransitive.Degree52FiveFixerFactorization

open MulAction

private theorem two_pow_dvd_bound
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (a : ℕ)
    (ha : 2 ^ a ∣ Nat.card (fixingSubgroup P s)) : a ≤ 20 := by
  have hfix : 5 ≤ Nat.card (fixedPoints (fixingSubgroup P s) X) := by
    rw [Nat.card_coe_set_eq,← hs]
    exact Set.ncard_le_ncard (by
      intro x hx q
      exact (mem_fixingSubgroup_iff P).mp q.property x hx)
  have hd := Degree52FiveGroupBound.card_dvd_exterior_tuples
    P hcard h5 hnotAlt (fixingSubgroup P s) 5 22 (by norm_num) hfix
  by_contra hn
  have hb : 2 ^ 21 ∣ Nat.card (fixingSubgroup P s) :=
    (pow_dvd_pow 2 (by omega : 21 ≤ a)).trans ha
  have hc := hb.trans hd
  norm_num [Nat.descFactorial] at hc

theorem card_exponents
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ∃ a b : ℕ, 1 ≤ a ∧ a ≤ 20 ∧ b ≤ 1 ∧
      Nat.card (fixingSubgroup P s) = 2 ^ a * 3 ^ b ∧
      Nat.card P = 311875200 * 2 ^ a * 3 ^ b := by
  let _ := h5
  have hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card (fixingSubgroup P s) →
      p = 2 ∨ p = 3 := by
    intro p hp hd
    have hlt : p < 11 := by
      by_contra hn
      exact Degree52LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs p hp (by omega) hd
    have hp5 : p ≠ 5 := by
      intro he; subst p
      exact Degree52FiveFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs hd
    have hp7 : p ≠ 7 := by
      intro he; subst p
      exact Degree52SevenFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs hd
    interval_cases p <;> norm_num at *
  obtain ⟨a,ha,b,hb,hH⟩ := Degree52FiveFixerArithmetic.factor_exponents Nat.card_pos.ne'
    (two_pow_dvd_bound P hcard h5 hnotAlt s hs)
    (Degree52ThreeSharpOrder.nine_not_dvd_five_fixer_card P hcard h5 hnotAlt s hs) hprimes
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
  refine ⟨a,b,ha0,ha,hb,hH,?_⟩
  rw [← hm]
  ring

theorem eleven_not_dvd_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    ¬ 11 ∣ Nat.card P := by
  classical
  obtain ⟨s,_,hs⟩ := Set.exists_subset_card_eq
    (show 5 ≤ (Set.univ : Set X).ncard by simp [Set.ncard_univ,hcard])
  obtain ⟨a,b,_,_,_,_,hP⟩ := card_exponents P hcard h5 hnotAlt s hs
  intro hd
  rw [hP] at hd
  have hp : Nat.Prime 11 := by decide
  rcases hp.dvd_mul.mp hd with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · norm_num at h
    · have hh := hp.dvd_of_dvd_pow h
      norm_num at hh
  · have hh := hp.dvd_of_dvd_pow h
    norm_num at hh

end FiveTransitive.Degree52FiveFixerFactorization

end CFSG
