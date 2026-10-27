module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.F918Z4c2Sl
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.Z4c2

open CFSG.Assembly.LowTwoRank CFSG.Quasithin

theorem statedScalars_subgroupOf_eq_bot {K : Type} [Field K] [CharP K 2] :
    (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) = ⊥ :=
  CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot

theorem nonempty_statedProj_mulEquiv_sl {K : Type} [Field K] [CharP K 2] :
    Nonempty (StatedProj (StatedSL 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) K) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_eq_bot (K := K))).trans
    QuotientGroup.quotientBot).trans (specialLinearGroupEquivStatedSL 2 K).symm⟩

theorem card_specialLinearGroup_two {K : Type} [Field K] [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  have := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem charP_two_of_card_eq_two_pow {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])

theorem exists_equiv_sl {L : Type} [Group L] {n : ℕ} (hL : IsPSL 2 2 n L) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ n ∧ 2 ≤ n ∧ Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨⟨-, hn1, -, h22, -⟩, K, _, _, hK, ⟨e⟩⟩ := hL
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have h1 : n = 1 := by omega
    subst h1
    exact h22 rfl
  have : CharP K 2 := charP_two_of_card_eq_two_pow hK
  obtain ⟨φ⟩ := nonempty_statedProj_mulEquiv_sl (K := K)
  exact ⟨K, inferInstance, inferInstance, this, hK, hn2, ⟨e.trans φ⟩⟩

theorem card_of_isPSL_two_two {L : Type} [Group L] {n : ℕ} (hL : IsPSL 2 2 n L) :
    Nat.card L = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  obtain ⟨K, _, _, _, hK, -, ⟨e⟩⟩ := exists_equiv_sl hL
  rw [Nat.card_congr e.toEquiv, card_specialLinearGroup_two, hK]

theorem exists_inverting {L : Type} [Group L] [Finite L] {n : ℕ} (hL : IsPSL 2 2 n L) (x : L) :
    ∃ w : L, w * x * w⁻¹ = x⁻¹ := by
  obtain ⟨K, _, _, _, -, -, ⟨e⟩⟩ := exists_equiv_sl hL
  obtain ⟨w, hw⟩ := exists_inverting_sl2 (e x)
  refine ⟨e.symm w, e.injective ?_⟩
  simpa [map_mul, map_inv] using hw

end CFSG.Quasithin.Z4c2
