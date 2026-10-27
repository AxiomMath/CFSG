module

public import CFSG.Permutation.FiveTransitive.Degree31FiveFixerSize
public import CFSG.Permutation.FiveTransitive.Degree31FiveFixerNumeric
public import CFSG.Permutation.FiveTransitive.Degree31FiveFixerNormalizer
public import CFSG.Permutation.FiveTransitive.Degree28ThirteenEven

public section

namespace CFSG

namespace FiveTransitive.Degree31FiveFixerArithmetic

open MulAction

private theorem card_and_exponents
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card (fixingSubgroup P s) → p = 2 ∨ p = 3)
    (h9 : ¬ 9 ∣ Nat.card (fixingSubgroup P s)) :
    ∃ a ≤ 12, ∃ b ≤ 1, Nat.card (fixingSubgroup P s) = 2 ^ a * 3 ^ b ∧
      Nat.card P = 20389320 * 2 ^ a * 3 ^ b := by
  have hsfix : s ⊆ fixedPoints (fixingSubgroup P s) X := by
    intro x hx q
    exact (mem_fixingSubgroup_iff P).mp q.property x hx
  have hfixed : 5 ≤ Nat.card (fixedPoints (fixingSubgroup P s) X) := by
    rw [Nat.card_coe_set_eq,← hs]
    exact Set.ncard_le_ncard hsfix
  have hdiv := Degree31FiveFixerSize.card_dvd_exterior_tuples
    P hcard h5 hnotAlt (fixingSubgroup P s) hfixed
  obtain ⟨a,ha,b,hb,hH⟩ := Degree31FiveFixerNumeric.factor_exponents
    (Nat.card_pos.ne') hdiv hprime h9
  have hi := IsMultiplyPretransitive.index_of_fixingSubgroup_eq s (by rwa [hs])
  rw [Nat.card_eq_fintype_card,hcard,hs] at hi
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial] at hi
  have hm := (fixingSubgroup P s).index_mul_card
  rw [hi,hH] at hm
  exact ⟨a,ha,b,hb,hH,by rw [← hm]; ring⟩

private theorem actual_normalizer_constraints
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {a b p : ℕ} (hp : p = 29 ∨ p = 31)
    (hP : Nat.card P = 20389320 * 2 ^ a * 3 ^ b) :
    ∃ d j : ℕ, d ∣ p - 1 ∧ (p = 29 → 2 ∣ d) ∧ j % p = 1 ∧
      d * j * p = 20389320 * 2 ^ a * 3 ^ b := by
  classical
  let _ : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> norm_num⟩
  let _ : Fintype P := Fintype.ofFinite P
  let _ : IsMultiplyPretransitive P X 5 := h5
  let _ : IsPretransitive P X := is_one_pretransitive_iff.mp
    (isMultiplyPretransitive_of_le (G := P) (α := X) (n := 5)
      (by norm_num : 1 ≤ 5) (by simp [hcard]))
  let S : Sylow p P := Sylow.nonempty.some
  have hS := Degree31FiveFixerNormalizer.sylow_card P hp hP S
  have hC := Degree31FiveFixerNormalizer.centralizer_card_dvd P hcard h5 hnotAlt hp S hS
  obtain ⟨hc,hr,_hcpos,_hrpos,hmod,hproduct⟩ :=
    Degree31FiveFixerNormalizer.normalizer_constraints P 1 S hS (by simpa using hC)
  let C : Subgroup P := Subgroup.centralizer (S : Set P)
  let N : Subgroup P := Subgroup.normalizer (S : Set P)
  let r := C.relIndex N
  have hcOne : (S : Subgroup P).relIndex C = 1 := Nat.dvd_one.mp hc
  change (S : Subgroup P).relIndex C * r * N.index * p = Nat.card P at hproduct
  rw [hcOne,one_mul] at hproduct
  have hNcard : Nat.card N = r * p := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < N.index from Nat.pos_of_ne_zero
      Subgroup.index_ne_zero_of_finite)
    calc
      N.index * Nat.card N = Nat.card P := N.index_mul_card
      _ = N.index * (r * p) := by rw [← hproduct]; ring
  refine ⟨r,N.index,hr,?_,hmod,by rwa [← hP]⟩
  intro hp29
  subst p
  have hevenN := Degree28ThirteenEven.normalizer_even P X S
    (Degree31FiveFixerNormalizer.sylow_twenty_nine_fixed_card P hcard S hS)
  change 2 ∣ Nat.card N at hevenN
  rw [hNcard] at hevenN
  rcases Nat.prime_two.dvd_mul.mp hevenN with h | h
  · exact h
  · norm_num at h

theorem five_fixer_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card (fixingSubgroup P s) → p = 2 ∨ p = 3)
    (h9 : ¬ 9 ∣ Nat.card (fixingSubgroup P s)) :
    Nat.card (fixingSubgroup P s) = 4096 := by
  obtain ⟨a,ha,b,hb,hH,hP⟩ := card_and_exponents P hcard h5 hnotAlt s hs hprime h9
  obtain ⟨d29,j29,hd29,heven,hj29,heq29⟩ :=
    actual_normalizer_constraints P hcard h5 hnotAlt (Or.inl rfl : 29 = 29 ∨ 29 = 31) hP
  obtain ⟨d31,j31,hd31,_heven31,hj31,heq31⟩ :=
    actual_normalizer_constraints P hcard h5 hnotAlt (Or.inr rfl : 31 = 29 ∨ 31 = 31) hP
  obtain ⟨rfl,rfl⟩ := Degree31FiveFixerNumeric.exponents_unique ha hb hd29 (heven rfl)
    hj29 heq29 hd31 hj31 heq31
  simpa using hH

end FiveTransitive.Degree31FiveFixerArithmetic

end CFSG
