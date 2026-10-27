module

public import CFSG.RankThree.PartOne.SLB4A.Index
public import CFSG.RankThree.PartOne.SLB4A.OrthB
public import CFSG.RankThree.PartOne.SLB4A.OrthD
public import CFSG.RankThree.PartOne.SLB4A.OrthDEven
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank TauCeti

theorem twoPowFive_typeB_odd {r : ℕ} {q : PrimePower} {hv : (LieTypeIndex.B r q).Valid}
    (hp : q.p ≠ 2) (hr : 3 ≤ r) {T : Type} [Group T]
    (e : T ≃* ValidLieTypeIndex.Group ⟨.B r q, hv⟩) :
    ∃ U : Subgroup T, IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨eK⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp hr e
  have hodd : Nat.card K % 2 = 1 := by
    rw [hKcard]
    exact Nat.odd_iff.1 ((q.prime_p.eq_two_or_odd'.resolve_left hp).pow)
  exact exists_of_mulEquiv eK (exists_two_pow_five_pomega_odd r hr (two_ne_zero_of_card_odd K hodd))

theorem twoPowFive_typeD {r : ℕ} {q : PrimePower} {hv : (LieTypeIndex.D r q).Valid}
    {T : Type} [Group T] (e : T ≃* ValidLieTypeIndex.Group ⟨.D r q, hv⟩) :
    ∃ U : Subgroup T, IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  obtain ⟨⟨-, -, hr⟩, K, hKf, hKfin, hKcard, ⟨eK⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e
  refine exists_of_mulEquiv eK ?_
  by_cases hp : q.p = 2
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := Fintype.ofFinite K
    have hc : Fintype.card K = 2 ^ q.exponent := by
      rw [← Nat.card_eq_fintype_card, hKcard, hp]
    have : CharP K 2 := charP_of_card_eq_prime_pow hc
    exact exists_two_pow_five_pomega_plus_even r hr
  · have hodd : Nat.card K % 2 = 1 := by
      rw [hKcard]
      exact Nat.odd_iff.1 ((q.prime_p.eq_two_or_odd'.resolve_left hp).pow)
    exact exists_two_pow_five_pomega_plus_odd r hr (two_ne_zero_of_card_odd K hodd)

theorem twoPowFive_typeTwistedD {r : ℕ} {q : PrimePower} {hv : (LieTypeIndex.twistedD r q).Valid}
    (hcase : (q.p ≠ 2 ∧ 4 ≤ r) ∨ (q.p = 2 ∧ 5 ≤ r)) {T : Type} [Group T]
    (e : T ≃* ValidLieTypeIndex.Group ⟨.twistedD r q, hv⟩) :
    ∃ U : Subgroup T, IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  obtain ⟨-, K, hKf, hKfin, hKcard, b, c, hbc, ⟨eK⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e
  refine exists_of_mulEquiv eK ?_
  rcases hcase with ⟨hp, hr⟩ | ⟨hp, hr⟩
  · have hodd : Nat.card K % 2 = 1 := by
      rw [hKcard]
      exact Nat.odd_iff.1 ((q.prime_p.eq_two_or_odd'.resolve_left hp).pow)
    exact exists_two_pow_five_pomega_minus_odd r hr b c hbc (two_ne_zero_of_card_odd K hodd)
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := Fintype.ofFinite K
    have hc : Fintype.card K = 2 ^ q.exponent := by
      rw [← Nat.card_eq_fintype_card, hKcard, hp]
    have : CharP K 2 := charP_of_card_eq_prime_pow hc
    exact exists_two_pow_five_pomega_minus_even r hr b c hbc

theorem twoPowFiveOf_typeB_odd : TwoPowFiveOf IsTypeBOddIndex := by
  intro i hi T _ ⟨e⟩
  cases i with
  | cyclic p hp => exact absurd hi (by simp [IsTypeBOddIndex])
  | alternating n hn => exact absurd hi (by simp [IsTypeBOddIndex])
  | sporadic s => exact absurd hi (by simp [IsTypeBOddIndex])
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | B r q => exact twoPowFive_typeB_odd hi.1 hi.2 e
    | _ => exact absurd hi (by simp [IsTypeBOddIndex])

theorem twoPowFiveOf_typeD : TwoPowFiveOf IsTypeDIndex := by
  intro i hi T _ ⟨e⟩
  cases i with
  | cyclic p hp => exact absurd hi (by simp [IsTypeDIndex])
  | alternating n hn => exact absurd hi (by simp [IsTypeDIndex])
  | sporadic s => exact absurd hi (by simp [IsTypeDIndex])
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | D r q => exact twoPowFive_typeD e
    | _ => exact absurd hi (by simp [IsTypeDIndex])

theorem twoPowFiveOf_typeTwistedD : TwoPowFiveOf IsTypeTwistedDIndex := by
  intro i hi T _ ⟨e⟩
  cases i with
  | cyclic p hp => exact absurd hi (by simp [IsTypeTwistedDIndex])
  | alternating n hn => exact absurd hi (by simp [IsTypeTwistedDIndex])
  | sporadic s => exact absurd hi (by simp [IsTypeTwistedDIndex])
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | twistedD r q => exact twoPowFive_typeTwistedD hi e
    | _ => exact absurd hi (by simp [IsTypeTwistedDIndex])

end CFSG.RankThree.PartOne.SLB4A
