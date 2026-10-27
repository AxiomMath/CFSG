module

public import CFSG.RankThree.PartOne.SLB4A.IndexExc
public import CFSG.RankThree.PartOne.SLB4A.ExcOddHcomb
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.Adapters.TauCetiExceptional.EvenAll

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti
  CFSG.TauCetiBridge.Even


theorem exists_equiv_adjointGroup {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hB : UntwistedBridgeAll τ c) (q : PrimePower) (hv : (c q).Valid) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q.card ∧
      Nonempty (ValidLieTypeIndex.Group ⟨c q, hv⟩ ≃* adjointGroup τ K) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', PrimePower.card_def]
  obtain ⟨e⟩ := hB q hv (GaloisField q.p q.exponent) hK
  exact nonempty_mulEquiv_adjointGroup τ (G := ValidLieTypeIndex.Group ⟨c q, hv⟩)
    ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hK, ⟨e.symm⟩⟩

theorem twoPowFive_typeE_odd_of {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hB : UntwistedBridgeAll τ c) {q : PrimePower} {hv : (c q).Valid} (hp : q.p ≠ 2)
    (a : Fin 5 → Fin τ.rank)
    (hcomb : ∀ v : V2 5, (∀ j : Fin τ.rank, sgp τ a 0 j ^ ex (v 0) * sgp τ a 1 j ^ ex (v 1) *
      sgp τ a 2 j ^ ex (v 2) * sgp τ a 3 j ^ ex (v 3) * sgp τ a 4 j ^ ex (v 4) = 1) → v = 1)
    {T : Type} [Group T] (e : T ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩) :
    ∃ U : Subgroup T, IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  obtain ⟨K, _, _, hK, ⟨e'⟩⟩ := exists_equiv_adjointGroup hB q hv
  have hodd : Nat.card K % 2 = 1 := by
    rw [hK, PrimePower.card_def]
    exact Nat.odd_iff.1 ((q.prime_p.eq_two_or_odd'.resolve_left hp).pow)
  exact exists_of_mulEquiv (e.trans e')
    (exists_two_pow_five_adjoint_odd a (neg_one_ne_one_of_card_odd K hodd) hcomb)

theorem twoPowFiveOf_typeEOdd (hB : ChevalleyBridgesAll) : TwoPowFiveOf IsTypeEOddIndex := by
  intro i hi T _ ⟨e⟩
  cases i with
  | cyclic p hp => exact absurd hi (by simp [IsTypeEOddIndex])
  | alternating n hn => exact absurd hi (by simp [IsTypeEOddIndex])
  | sporadic s => exact absurd hi (by simp [IsTypeEOddIndex])
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | E6 q => exact twoPowFive_typeE_odd_of hB.e6 hi _ hcombE6 e
    | E7 q => exact twoPowFive_typeE_odd_of hB.e7 hi _ hcombE7 e
    | E8 q => exact twoPowFive_typeE_odd_of hB.e8 hi _ hcombE8 e
    | _ => exact absurd hi (by simp [IsTypeEOddIndex])

end CFSG.RankThree.PartOne.SLB4A
