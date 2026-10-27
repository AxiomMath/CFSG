module

public import CFSG.RankThree.PartOne.SLB4A.Index
public import CFSG.RankThree.PartOne.SLB4A.TypeA
public import CFSG.RankThree.PartOne.SLB4A.TypeSU
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank TauCeti

theorem twoPowFive_typeA {r : ℕ} {q : PrimePower} {hv : (LieTypeIndex.A r q).Valid}
    (hcase : (q.p = 2 ∧ 4 ≤ r) ∨ (q.p ≠ 2 ∧ r = 5 ∧ q.card % 4 = 1) ∨ (q.p ≠ 2 ∧ 6 ≤ r))
    {T : Type} [Group T] (e : T ≃* ValidLieTypeIndex.Group ⟨.A r q, hv⟩) :
    ∃ U : Subgroup T, IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  refine exists_of_mulEquiv (e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
    (projectiveSpecialLinearGroupEquivStatedProj (r + 1) (GaloisField q.p q.exponent)))) ?_
  have hodd : q.p ≠ 2 → Nat.card (GaloisField q.p q.exponent) % 2 = 1 := fun hp => by
    rw [hK]
    exact Nat.odd_iff.1 ((q.prime_p.eq_two_or_odd'.resolve_left hp).pow)
  rcases hcase with ⟨hp, hr⟩ | ⟨hp, rfl, h4⟩ | ⟨hp, hr⟩
  · have : CharP (GaloisField q.p q.exponent) 2 := hp ▸ (inferInstance : CharP _ q.p)
    exact exists_two_pow_five_psl_even (r + 1) (by omega)
  · have h2 := neg_one_ne_one_of_card_odd _ (hodd hp)
    obtain ⟨u, hu⟩ := exists_sq_neg_one (GaloisField q.p q.exponent) (by
      rw [hK]
      simpa [PrimePower.card_def] using h4)
    exact exists_two_pow_five_psl_six h2 u hu
  · exact exists_two_pow_five_psl_odd (r + 1) (by omega) (neg_one_ne_one_of_card_odd _ (hodd hp))

theorem twoPowFive_typeTwistedA {r : ℕ} {q : PrimePower} {hv : (LieTypeIndex.twistedA r q).Valid}
    (hcase : (q.p = 2 ∧ 5 ≤ r) ∨ (q.p ≠ 2 ∧ r = 5 ∧ q.card % 4 = 3) ∨ (q.p ≠ 2 ∧ 6 ≤ r))
    {T : Type} [Group T] (e : T ≃* ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) :
    ∃ U : Subgroup T, IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨eK⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  refine exists_of_mulEquiv eK ?_
  have hq : q.p ^ q.exponent = q.card := by rw [PrimePower.card_def]
  have hKc : Nat.card K = q.card ^ 2 := by rw [hKcard, hq]
  have hQodd : q.p ≠ 2 → Odd (q.p ^ q.exponent) := fun hp =>
    (q.prime_p.eq_two_or_odd'.resolve_left hp).pow
  have hodd : q.p ≠ 2 → Nat.card K % 2 = 1 := fun hp => by
    rw [hKcard]
    exact Nat.odd_iff.1 ((hQodd hp).pow)
  rcases hcase with ⟨hp, hr⟩ | ⟨hp, rfl, h4⟩ | ⟨hp, hr⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := Fintype.ofFinite K
    have hc : Fintype.card K = 2 ^ (2 * q.exponent) := by
      rw [← Nat.card_eq_fintype_card, hKcard, hp, ← pow_mul, mul_comm]
    have : CharP K 2 := charP_of_card_eq_prime_pow hc
    exact exists_two_pow_five_psu_even (Nat.pos_of_ne_zero (pow_ne_zero _ q.prime_p.ne_zero)) (r + 1) (by omega)
  · have h2 := neg_one_ne_one_of_card_odd K (hodd hp)
    have hK4 : Nat.card K % 4 = 1 := by
      rw [hKc, pow_two, Nat.mul_mod, h4]
    obtain ⟨u, hu⟩ := exists_sq_neg_one K hK4
    have huq : (u : K) ^ (q.p ^ q.exponent) * u = 1 := by
      rw [hq]
      have hev : Even ((q.card + 1) / 2) := ⟨(q.card + 1) / 4, by omega⟩
      calc (u : K) ^ q.card * u = (u : K) ^ (q.card + 1) := (pow_succ _ _).symm
        _ = (u : K) ^ (2 * ((q.card + 1) / 2)) := by congr 1; omega
        _ = ((u : K) ^ 2) ^ ((q.card + 1) / 2) := pow_mul _ _ _
        _ = (-1) ^ ((q.card + 1) / 2) := by rw [sq, hu]
        _ = 1 := hev.neg_one_pow
    exact exists_two_pow_five_psu_six (hQodd hp) h2 u hu huq
  · exact exists_two_pow_five_psu_odd (hQodd hp) (r + 1) (by omega)
      (neg_one_ne_one_of_card_odd K (hodd hp))

theorem twoPowFiveOf_typeA : TwoPowFiveOf IsTypeAIndex := by
  intro i hi T _ ⟨e⟩
  cases i with
  | cyclic p hp => exact absurd hi (by simp [IsTypeAIndex])
  | alternating n hn => exact absurd hi (by simp [IsTypeAIndex])
  | sporadic s => exact absurd hi (by simp [IsTypeAIndex])
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | A r q => exact twoPowFive_typeA hi e
    | _ => exact absurd hi (by simp [IsTypeAIndex])

theorem twoPowFiveOf_typeTwistedA : TwoPowFiveOf IsTypeTwistedAIndex := by
  intro i hi T _ ⟨e⟩
  cases i with
  | cyclic p hp => exact absurd hi (by simp [IsTypeTwistedAIndex])
  | alternating n hn => exact absurd hi (by simp [IsTypeTwistedAIndex])
  | sporadic s => exact absurd hi (by simp [IsTypeTwistedAIndex])
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | twistedA r q => exact twoPowFive_typeTwistedA hi e
    | _ => exact absurd hi (by simp [IsTypeTwistedAIndex])

end CFSG.RankThree.PartOne.SLB4A
