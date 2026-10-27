module

public import CFSG.Permutation.FiveTransitive.Degree60FourPrimeArithmetic
public import CFSG.Permutation.FiveTransitive.Degree60FiveFixerSmallWindowNumeric
public import CFSG.Permutation.FiveTransitive.Degree60TupleBounds
public import CFSG.Permutation.FiveTransitive.Degree60LargePrimeConstraints
public import CFSG.Permutation.FiveTransitive.Degree60SevenFree
public import CFSG.Permutation.FiveTransitive.HighDegreeHallReduction

public section

namespace CFSG

namespace FiveTransitive.Degree60FiveFixerSmallWindow
open MulAction

private theorem prime_exponent_bound
    {H : Type*} [Group H] [Finite H] (p k : ℕ) (hp : p.Prime)
    (hS : ∀ S : Sylow p H, Nat.card S ≤ p^k)
    (a : ℕ) (ha : p^a ∣ Nat.card H) : a ≤ k := by
  let _ : Fact p.Prime := ⟨hp⟩
  let S : Sylow p H := Sylow.nonempty.some
  have hd : p^a ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card ha
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp
    ((Nat.le_of_dvd Nat.card_pos hd).trans (hS S))

theorem excluded_of_sylow_bounds
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hthree : ∀ S : Sylow 3 (fixingSubgroup P s), Nat.card S ≤ 729)
    (hfive : ∀ S : Sylow 5 (fixingSubgroup P s), Nat.card S ≤ 5)
    (heleven : ∀ S : Sylow 11 (fixingSubgroup P s), Nat.card S ≤ 11) : False := by
  let _ := h5
  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card (fixingSubgroup P s) →
      p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 11 := by
    intro p hp hd
    have hlt : p < 13 := by
      by_contra hn
      exact Degree60LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs p hp (by omega) hd
    have hp7 : p ≠ 7 := by
      intro he; subst p
      exact Degree60SevenFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs hd
    interval_cases p <;> norm_num at *
  have hb := prime_exponent_bound 3 6 (by decide : Nat.Prime 3)
    (fun S : Sylow 3 (fixingSubgroup P s) => by simpa using hthree S)
  have hc := prime_exponent_bound 5 1 (by decide : Nat.Prime 5)
    (fun S : Sylow 5 (fixingSubgroup P s) => by simpa using hfive S)
  have he := prime_exponent_bound 11 1 (by decide : Nat.Prime 11)
    (fun S : Sylow 11 (fixingSubgroup P s) => by simpa using heleven S)
  obtain ⟨a,ha,b,hb,c,hc,e,he,hH⟩ := Degree60FourPrimeArithmetic.factor_exponents Nat.card_pos.ne'
    (Degree60TupleBounds.two_pow_dvd_bound P hcard h5 hnotAlt s hs) hb hc he hprime
  have ha0 : 1 ≤ a := by
    have heven := Research.HighDegreeHallReduction.even_card_fixingSubgroup_of_five_transitive
      X P (by omega) h5 s hs
    have hd := even_iff_two_dvd.mp heven
    by_contra hn
    have haeq : a = 0 := by omega
    rw [hH,haeq,pow_zero,one_mul] at hd
    rcases Nat.prime_two.dvd_mul.mp hd with h | h
    · rcases Nat.prime_two.dvd_mul.mp h with h | h
      · have hh := Nat.prime_two.dvd_of_dvd_pow h
        norm_num at hh
      · have hh := Nat.prime_two.dvd_of_dvd_pow h
        norm_num at hh
    · have hh := Nat.prime_two.dvd_of_dvd_pow h
      norm_num at hh
  have hi := IsMultiplyPretransitive.index_of_fixingSubgroup_eq (G := P) s (by rwa [hs])
  rw [Nat.card_eq_fintype_card,hcard,hs] at hi
  norm_num [Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial] at hi
  have hm := (fixingSubgroup P s).index_mul_card
  rw [hi,hH] at hm
  have hP : Nat.card P = 655381440 * 2^a * 3^b * 5^c * 11^e := by rw [← hm]; ring
  obtain ⟨d59,k59,hd59,hf59,hk59,he59⟩ := Degree60LargePrimeConstraints.constraints
    P hcard h5 hnotAlt (Or.inl rfl)
  obtain ⟨d29,k29,hd29,hf29,hk29,he29⟩ := Degree60LargePrimeConstraints.constraints
    P hcard h5 hnotAlt (Or.inr (Or.inl rfl))
  obtain ⟨d19,k19,hd19,hf19,hk19,he19⟩ := Degree60LargePrimeConstraints.constraints
    P hcard h5 hnotAlt (Or.inr (Or.inr rfl))
  norm_num [Nat.factorial] at hd59 hf59 hd29 hf29 hd19 hf19
  rw [hP] at he59 he29 he19
  exact Degree60FiveFixerSmallWindowNumeric.excluded ha0 ha hb hc he
    (Degree60FiveFixerSmallWindowNumeric.fifty_nine_residue hd59 (one_dvd _) hk59 he59)
    (Degree60FiveFixerSmallWindowNumeric.twenty_nine_residue hd29 hf29 hk29 he29)
    (Degree60FiveFixerSmallWindowNumeric.nineteen_residue hd19 hf19 hk19 he19)

end FiveTransitive.Degree60FiveFixerSmallWindow

end CFSG
