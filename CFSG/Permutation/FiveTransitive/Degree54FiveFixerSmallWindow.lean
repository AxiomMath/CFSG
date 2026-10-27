module

public import CFSG.Permutation.FiveTransitive.Degree54FiveFixerFactorization
public import CFSG.Permutation.FiveTransitive.Degree54FiveFixerNumeric
public import CFSG.Permutation.FiveTransitive.Degree54LargePrimeConstraints
public import CFSG.Permutation.FiveTransitive.Degree54TwoLowerBound

public section

namespace CFSG

namespace FiveTransitive.Degree54FiveFixerSmallWindow
open MulAction

private theorem sylow_cards
    {H : Type*} [Group H] [Finite H] {a b : ℕ}
    (hH : Nat.card H = 2^a * 3^b) (S : Sylow 2 H) (T : Sylow 3 H) :
    Nat.card S = 2^a ∧ Nat.card T = 3^b := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h2 : (2^a : ℕ) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : (3^b : ℕ) ≠ 0 := pow_ne_zero _ (by norm_num)
  constructor
  · rw [S.card_eq_multiplicity,hH,Nat.factorization_mul h2 h3,Finsupp.add_apply]
    norm_num [Nat.factorization_pow,Nat.prime_two.factorization,
      (show Nat.Prime 3 by decide).factorization]
  · rw [T.card_eq_multiplicity,hH,Nat.factorization_mul h2 h3,Finsupp.add_apply]
    norm_num [Nat.factorization_pow,Nat.prime_two.factorization,
      (show Nat.Prime 3 by decide).factorization]

theorem sylow_orders_of_two_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 2 (fixingSubgroup P s)) (hS : Nat.card S ≤ 512)
    (T : Sylow 3 (fixingSubgroup P s)) : Nat.card S = 512 ∧ Nat.card T = 27 := by
  obtain ⟨a,b,_,_,hb,hH,hP⟩ := Degree54FiveFixerFactorization.card_exponents P hcard h5 hnotAlt s hs
  obtain ⟨hSCard,hTCard⟩ := sylow_cards hH S T
  have h16 := Degree54TwoLowerBound.sylow_sixteen_le P hcard h5 hnotAlt s hs S
  rw [hSCard] at h16 hS
  have ha0 : 4 ≤ a := by
    by_contra hn
    interval_cases a <;> norm_num at h16
  have ha : a ≤ 9 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 10 ≤ a)
    norm_num at hh
    omega
  obtain ⟨d53,k53,hd53,hf53,hk53,he53⟩ := Degree54LargePrimeConstraints.constraints
    P hcard h5 hnotAlt (Or.inl rfl)
  obtain ⟨d17,k17,hd17,hf17,hk17,he17⟩ := Degree54LargePrimeConstraints.constraints
    P hcard h5 hnotAlt (Or.inr (Or.inl rfl))
  obtain ⟨d13,k13,hd13,hf13,hk13,he13⟩ := Degree54LargePrimeConstraints.constraints
    P hcard h5 hnotAlt (Or.inr (Or.inr rfl))
  norm_num [Nat.factorial] at hd53 hf53 hd17 hf17 hd13 hf13
  rw [hP] at he53 he17 he13
  have r53 := Degree54FiveFixerNumeric.fifty_three_residue hd53 (one_dvd _) hk53 he53
  have r17 := Degree54FiveFixerNumeric.seventeen_residue hd17 hf17 hk17 he17
  have r13 := Degree54FiveFixerNumeric.thirteen_residue hd13 hf13 hk13 he13
  obtain ⟨rfl,rfl⟩ := Degree54FiveFixerNumeric.exponents_through_nine ha0 ha hb r53 r17 r13
  norm_num at hSCard hTCard
  exact ⟨hSCard,hTCard⟩

end FiveTransitive.Degree54FiveFixerSmallWindow

end CFSG
