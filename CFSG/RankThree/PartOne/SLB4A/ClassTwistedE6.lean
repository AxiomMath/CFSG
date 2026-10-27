module

public import CFSG.RankThree.PartOne.SLB4A.TwistE6Orbit
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.RankThree.PartOne.SLB4A.IndexExc

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti
  CFSG.TauCetiBridge.Even

theorem charP_two_of_card_pow {K : Type} [Field K] [Finite K] {q : PrimePower} (hp : q.p = 2)
    {m : ℕ} (hK : Nat.card K = q.card ^ m) : CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Fintype.card K = 2 ^ (q.exponent * m) := by
    rw [← Nat.card_eq_fintype_card, hK, PrimePower.card_def, hp, pow_mul]
  exact charP_of_card_eq_prime_pow hc

section Bridge


theorem exists_equiv_graphFixedRootGroup {c : PrimePower → LieTypeIndex}
    (hB : TwistedBridgeAll .E6 c) (q : PrimePower) (hv : (c q).Valid) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K),
      Nat.card K = q.card ^ TwistTag.E6.order ∧ (∀ x, σ x = x ^ q.card) ∧
        Nonempty (ValidLieTypeIndex.Group ⟨c q, hv⟩ ≃* graphFixedRootGroup TwistTag.E6 K σ) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hm : 0 < TwistTag.E6.order := by decide
  have hK : Nat.card (GaloisField q.p (q.exponent * TwistTag.E6.order)) =
      q.card ^ TwistTag.E6.order := by
    rw [GaloisField.card q.p (q.exponent * TwistTag.E6.order)
      (Nat.mul_ne_zero q.exponent_pos.ne' hm.ne'), PrimePower.card_def, pow_mul]
  let σ : GaloisField q.p (q.exponent * TwistTag.E6.order) →+*
      GaloisField q.p (q.exponent * TwistTag.E6.order) :=
    iterateFrobenius (GaloisField q.p (q.exponent * TwistTag.E6.order)) q.p q.exponent
  have hσ : ∀ x, σ x = x ^ q.card := fun x => by
    rw [iterateFrobenius_def, PrimePower.card_def]
  obtain ⟨φ⟩ := hB q hv (GaloisField q.p (q.exponent * TwistTag.E6.order)) hK σ hσ
  have hmodel : TwistedChevalleyModel (ValidLieTypeIndex.Group ⟨c q, hv⟩) .E6
      (q.p ^ q.exponent) :=
    ⟨GaloisField q.p (q.exponent * TwistTag.E6.order), inferInstance, inferInstance,
      by rw [hK, PrimePower.card_def], σ, fun x => by rw [hσ, PrimePower.card_def], ⟨φ.symm⟩⟩
  obtain ⟨K, _, _, σ', hK', hσ', ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .E6 q.prime_p q.exponent_pos hmodel
  refine ⟨K, inferInstance, inferInstance, σ'.toRingHom, ?_, fun x => ?_, ⟨e⟩⟩
  · rw [hK', PrimePower.card_def]
  · rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ', PrimePower.card_def]

theorem twoPowFiveOf_typeTwistedE6Odd (hB : ChevalleyBridgesAll) :
    TwoPowFiveOf IsTypeTwistedE6OddIndex := by
  intro i hi T _ ⟨e⟩
  cases i with
  | cyclic p hp => exact absurd hi (by simp [IsTypeTwistedE6OddIndex])
  | alternating n hn => exact absurd hi (by simp [IsTypeTwistedE6OddIndex])
  | sporadic s => exact absurd hi (by simp [IsTypeTwistedE6OddIndex])
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | twistedE6 q =>
      obtain ⟨K, _, _, σ, hK, hσ, ⟨e'⟩⟩ := exists_equiv_graphFixedRootGroup hB.twistedE6 q hv
      have hodd : Nat.card K % 2 = 1 := by
        rw [hK, PrimePower.card_def]
        exact Nat.odd_iff.1 ((q.prime_p.eq_two_or_odd'.resolve_left hi).pow.pow)
      exact exists_of_mulEquiv (e.trans e')
        (exists_two_pow_five_twistedE6_odd σ (neg_one_ne_one_of_card_odd K hodd))
    | _ => exact absurd hi (by simp [IsTypeTwistedE6OddIndex])

theorem twoPowFiveOf_typeTwistedE6Even (hB : ChevalleyBridgesAll) :
    TwoPowFiveOf IsTypeTwistedE6EvenIndex := by
  intro i hi T _ ⟨e⟩
  cases i with
  | cyclic p hp => exact absurd hi (by simp [IsTypeTwistedE6EvenIndex])
  | alternating n hn => exact absurd hi (by simp [IsTypeTwistedE6EvenIndex])
  | sporadic s => exact absurd hi (by simp [IsTypeTwistedE6EvenIndex])
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | twistedE6 q =>
      obtain ⟨K, _, _, σ, hK, hσ, ⟨e'⟩⟩ := exists_equiv_graphFixedRootGroup hB.twistedE6 q hv
      have := charP_two_of_card_pow hi hK
      exact exists_of_mulEquiv (e.trans e') (exists_two_pow_five_twistedE6_even σ)
    | _ => exact absurd hi (by simp [IsTypeTwistedE6EvenIndex])

end Bridge

end CFSG.RankThree.PartOne.SLB4A
