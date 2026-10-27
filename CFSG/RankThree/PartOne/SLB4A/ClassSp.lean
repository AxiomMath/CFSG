module

public import CFSG.RankThree.PartOne.SLB4A.Index
public import CFSG.RankThree.PartOne.SLB4A.SpEven
public import CFSG.RankThree.PartOne.SLB4A.SpOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank TauCeti

theorem exists_two_pow_five_psp {r p f : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p ^ f) (hr : 4 ≤ r) :
    ∃ U : Subgroup (StatedProj (StatedSp r K)), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  by_cases h2 : p = 2
  · subst h2
    have : Fact (Nat.Prime 2) := ⟨hp⟩
    have := Fintype.ofFinite K
    have hc : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card, hK]
    have : CharP K 2 := charP_of_card_eq_prime_pow hc
    exact exists_two_pow_five_psp_even (by omega)
  · have hodd : Nat.card K % 2 = 1 := by
      rw [hK]
      exact Nat.odd_iff.1 ((hp.eq_two_or_odd'.resolve_left h2).pow)
    obtain ⟨x, y, hxy⟩ := exists_sq_add_sq_neg_one K hodd
    exact exists_two_pow_five_psp_odd hr (neg_one_ne_one_of_card_odd K hodd) hxy

theorem twoPowFive_typeC {r : ℕ} {q : PrimePower} {hv : (LieTypeIndex.C r q).Valid} (hr : 4 ≤ r)
    {T : Type} [Group T] (e : T ≃* ValidLieTypeIndex.Group ⟨.C r q, hv⟩) :
    ∃ U : Subgroup T, IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨eK⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e
  exact exists_of_mulEquiv eK (exists_two_pow_five_psp q.prime_p hKcard hr)

theorem twoPowFive_typeB_even {r : ℕ} {q : PrimePower} {hv : (LieTypeIndex.B r q).Valid}
    (hp : q.p = 2) (hr : 4 ≤ r) {T : Type} [Group T]
    (e : T ≃* ValidLieTypeIndex.Group ⟨.B r q, hv⟩) :
    ∃ U : Subgroup T, IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨eK⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp (by omega) e
  exact exists_of_mulEquiv eK (exists_two_pow_five_psp q.prime_p hKcard hr)

theorem twoPowFiveOf_typeC : TwoPowFiveOf IsTypeCIndex := by
  intro i hi T _ ⟨e⟩
  cases i with
  | cyclic p hp => exact absurd hi (by simp [IsTypeCIndex])
  | alternating n hn => exact absurd hi (by simp [IsTypeCIndex])
  | sporadic s => exact absurd hi (by simp [IsTypeCIndex])
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | C r q => exact twoPowFive_typeC hi e
    | _ => exact absurd hi (by simp [IsTypeCIndex])

theorem twoPowFiveOf_typeB_even : TwoPowFiveOf IsTypeBEvenIndex := by
  intro i hi T _ ⟨e⟩
  cases i with
  | cyclic p hp => exact absurd hi (by simp [IsTypeBEvenIndex])
  | alternating n hn => exact absurd hi (by simp [IsTypeBEvenIndex])
  | sporadic s => exact absurd hi (by simp [IsTypeBEvenIndex])
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | B r q => exact twoPowFive_typeB_even hi.1 hi.2 e
    | _ => exact absurd hi (by simp [IsTypeBEvenIndex])

end CFSG.RankThree.PartOne.SLB4A
