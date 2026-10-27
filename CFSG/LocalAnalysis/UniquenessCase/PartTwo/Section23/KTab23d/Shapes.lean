module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.Open

private theorem charP_two_D4 {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : f ≠ 0) : CharP K 2 := by
  have h : Nat.card K • (1 : K) = 0 := card_nsmul_eq_zero'
  rw [hK, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat] at h
  exact CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero ((pow_eq_zero_iff hf).mp h)

theorem isL2_of_mulEquiv_sl2 {X : Type} [Group X] {K : Type} [Field K] [Finite K] {f : ℕ}
    (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    IsL2 X f := by
  haveI : CharP K 2 := charP_two_D4 hK (by omega)
  have hbot : (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) = ⊥ :=
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot
  let q : StatedProj (StatedSL 2 K) ≃* ↥(StatedSL 2 K) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hadm : StatedLieAdmissible .PSL 2 2 f := by
    refine ⟨Nat.prime_two, by omega, by omega, ?_, ?_⟩
    · intro h
      have h2 : 2 ^ f = 2 := congrArg Prod.snd h
      rw [h2] at h4
      omega
    · intro h
      have h3 : 2 ^ f = 3 := congrArg Prod.snd h
      rw [h3] at h4
      omega
  exact Or.inl ⟨by decide, ⟨hadm, K, inferInstance, inferInstance, hK,
    ⟨(e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)).trans q.symm⟩⟩⟩

theorem isSp4_of_mulEquiv_statedSp {X : Type} [Group X] {K : Type} [Field K] [Finite K] {f : ℕ}
    (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) (e : X ≃* ↥(CFSG.Open.StatedSp 2 K)) :
    IsSp4 X f := by
  haveI : CharP K 2 := charP_two_D4 hK (by omega)
  have hbot : (StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K) = ⊥ :=
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot
  let q : StatedProj (StatedSp 2 K) ≃* ↥(StatedSp 2 K) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hadm : StatedLieAdmissible .PSp 2 2 f := by
    refine ⟨Nat.prime_two, by omega, by omega, ?_⟩
    intro h
    have h2 : 2 ^ f = 2 := congrArg Prod.snd h
    rw [h2] at h4
    omega
  exact Or.inl ⟨by decide, ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e.trans q.symm⟩⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
