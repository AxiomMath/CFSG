module

public import CFSG.RankThree.PartOne.SLB4A.ClassExc
public import CFSG.RankThree.PartOne.SLB4A.ExcEven
public import CFSG.RankThree.PartOne.SLB4A.F4Odd

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti
  CFSG.TauCetiBridge.Even

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {q : PrimePower} (hp : q.p = 2)
    (hK : Nat.card K = q.card) : CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Fintype.card K = 2 ^ q.exponent := by
    rw [← Nat.card_eq_fintype_card, hK, PrimePower.card_def, hp]
  exact charP_of_card_eq_prime_pow hc


theorem twoPowFive_typeExc_even_of {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hB : UntwistedBridgeAll τ c) {q : PrimePower} {hv : (c q).Valid} (hp : q.p = 2)
    (hex : ∀ (K : Type) [Field K] [CharP K 2],
      ∃ U : Subgroup (adjointGroup τ K), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5)
    {T : Type} [Group T] (e : T ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩) :
    ∃ U : Subgroup T, IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  obtain ⟨K, _, _, hK, ⟨e'⟩⟩ := exists_equiv_adjointGroup hB q hv
  have := charP_two_of_card hp hK
  exact exists_of_mulEquiv (e.trans e') (hex K)

theorem twoPowFiveOf_typeEEven (hB : ChevalleyBridgesAll) : TwoPowFiveOf IsTypeEEvenIndex := by
  intro i hi T _ ⟨e⟩
  cases i with
  | cyclic p hp => exact absurd hi (by simp [IsTypeEEvenIndex])
  | alternating n hn => exact absurd hi (by simp [IsTypeEEvenIndex])
  | sporadic s => exact absurd hi (by simp [IsTypeEEvenIndex])
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | E6 q => exact twoPowFive_typeExc_even_of hB.e6 hi (fun K => exists_two_pow_five_E6_even) e
    | E7 q => exact twoPowFive_typeExc_even_of hB.e7 hi (fun K => exists_two_pow_five_E7_even) e
    | E8 q => exact twoPowFive_typeExc_even_of hB.e8 hi (fun K => exists_two_pow_five_E8_even) e
    | _ => exact absurd hi (by simp [IsTypeEEvenIndex])

theorem twoPowFiveOf_typeF4Even (hB : ChevalleyBridgesAll) : TwoPowFiveOf IsTypeF4EvenIndex := by
  intro i hi T _ ⟨e⟩
  cases i with
  | cyclic p hp => exact absurd hi (by simp [IsTypeF4EvenIndex])
  | alternating n hn => exact absurd hi (by simp [IsTypeF4EvenIndex])
  | sporadic s => exact absurd hi (by simp [IsTypeF4EvenIndex])
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | F4 q => exact twoPowFive_typeExc_even_of hB.f4 hi (fun K => exists_two_pow_five_F4_even) e
    | _ => exact absurd hi (by simp [IsTypeF4EvenIndex])

theorem twoPowFiveOf_typeF4Odd (hB : ChevalleyBridgesAll) : TwoPowFiveOf IsTypeF4OddIndex := by
  intro i hi T _ ⟨e⟩
  cases i with
  | cyclic p hp => exact absurd hi (by simp [IsTypeF4OddIndex])
  | alternating n hn => exact absurd hi (by simp [IsTypeF4OddIndex])
  | sporadic s => exact absurd hi (by simp [IsTypeF4OddIndex])
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | F4 q =>
      obtain ⟨K, _, _, hK, ⟨e'⟩⟩ := exists_equiv_adjointGroup hB.f4 q hv
      have hodd : Nat.card K % 2 = 1 := by
        rw [hK, PrimePower.card_def]
        exact Nat.odd_iff.1 ((q.prime_p.eq_two_or_odd'.resolve_left hi).pow)
      exact exists_of_mulEquiv (e.trans e')
        (exists_two_pow_five_F4_odd (neg_one_ne_one_of_card_odd K hodd))
    | _ => exact absurd hi (by simp [IsTypeF4OddIndex])

end CFSG.RankThree.PartOne.SLB4A
