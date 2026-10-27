module

public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.OddL2Big
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.OddL3U3
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.G11.Harris
  CFSG.Assembly.LowTwoRank CFSG.SectionRank.OddCover
  CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

theorem center_statedSL_eq_scalars (K : Type) [Field K] :
    Subgroup.center (StatedSL 3 K) = (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) := by
  rw [← map_center_eq_statedScalars 3 K]
  exact (Subgroup.map_center_eq (specialLinearGroupEquivStatedSL 3 K)).symm

theorem statedProj_quotient_center_SL {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hK : Nat.card K = p) (e : X ≃* StatedSL 3 K) :
    StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 3 p 1 := by
  refine ⟨⟨hp, le_rfl, by norm_num, ?_, ?_⟩, K, inferInstance, inferInstance, by rw [pow_one, hK],
    ⟨?_⟩⟩
  · simp only [pow_one, ne_eq, Prod.mk.injEq, not_and]
    intro _ h
    omega
  · simp only [pow_one, ne_eq, Prod.mk.injEq, not_and]
    intro _ h
    omega
  · refine QuotientGroup.congr _ _ e ?_
    rw [← center_statedSL_eq_scalars]
    exact Subgroup.map_center_eq e

theorem statedProj_quotient_center_SU {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hK : Nat.card K = p ^ 2) (e : X ≃* StatedSU 3 p K) :
    StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 p 1 ∧
      Subgroup.center (StatedSU 3 p K) =
        (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 p K) := by
  have hK' : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one, hK]
  have hnq : ((3 : ℕ), p ^ 1) ≠ (3, 2) := by
    simp only [pow_one, ne_eq, Prod.mk.injEq, true_and]
    exact hp2
  have hcen1 : Subgroup.center (StatedSU 3 (p ^ 1) K) =
      (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ 1) K) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := p) (f := 1) hK'
      le_rfl hnq).2
  have e' : X ≃* ↥(StatedSU 3 (p ^ 1) K) := by rw [pow_one]; exact e
  have hcen := hcen1
  rw [pow_one] at hcen
  refine ⟨⟨⟨Fact.out, le_rfl, le_rfl, hnq⟩, K, inferInstance, inferInstance, hK',
    ⟨QuotientGroup.congr _ _ e' ?_⟩⟩, hcen⟩
  rw [← hcen1]
  exact Subgroup.map_center_eq e'

theorem card_center_statedSU_three_dvd {K : Type} [Field K] [Finite K] {p : ℕ}
    [Fact p.Prime] (hK : Nat.card K = p ^ 2)
    (hcen : Subgroup.center (StatedSU 3 p K) =
      (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 p K)) :
    Nat.card (Subgroup.center (StatedSU 3 p K)) ∣ 3 ∧
      Nat.card (Subgroup.center (StatedSU 3 p K)) ∣ p + 1 := by
  have hK' : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one, hK]
  have := Fintype.ofFinite K
  have hchar : CharP K p :=
    charP_of_card_eq_prime_pow (p := p) (f := 2) (by rw [← Nat.card_eq_fintype_card, hK])
  rw [hcen]
  have hH : (Nat.card K = p ^ 1 ∧ StatedSU 3 p K = StatedSL 3 K) ∨
      (Nat.card K = (p ^ 1) ^ 2 ∧ StatedSU 3 p K = StatedSU 3 (p ^ 1) K) :=
    Or.inr ⟨hK', by rw [pow_one]⟩
  refine ⟨card_scalars_dvd (by norm_num) _ fun x c hc => ?_,
    card_scalars_dvd (by norm_num) _ fun x c hc => ?_⟩
  · have hdet := det_eq_one_of_linUni (p := p) (f := 1) (n := 3) hH x.1.2
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
  · have hu := unitary_of_mem_statedSU (p := p) (f := 1) (n := 3) hK' (by rw [pow_one]; exact x.1.2)
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar] at hu
    have h00 := congrFun (congrFun hu ⟨0, by norm_num⟩) ⟨0, by norm_num⟩
    have hq0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
    rw [Matrix.scalar_apply, Matrix.diagonal_map (by simp [zero_pow hq0]),
      Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.one_apply_eq,
      Matrix.diagonal_apply_eq] at h00
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_succ, Units.val_one]
    simpa [pow_one] using h00

theorem oneCompFor_famCoverOdd : OneCompFor FamCoverOdd := by
  intro V _ _ _ Γ A L m hs ⟨hcen, s, p, hp, hp2, hX⟩
  exfalso
  have h := g93Hyp_of_oneCompSetting hs
  have : Fact p.Prime := ⟨hp⟩
  cases s with
  | true =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hX
    exact false_of_oddL3 hp2 h (statedProj_quotient_center_SL hp hK e)
  | false =>
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hX
    obtain ⟨hmod, hcenH⟩ := statedProj_quotient_center_SU hp2 hK e
    have hp3 : p = 3 := oddU3_reduce hp2 h hmod
    subst hp3
    obtain ⟨hd3, hd4⟩ := card_center_statedSU_three_dvd hK hcenH
    have hcard : Nat.card (Subgroup.center (StatedSU 3 3 K)) = 3 := by
      rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]
      exact hcen
    rw [hcard] at hd4
    omega

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent
