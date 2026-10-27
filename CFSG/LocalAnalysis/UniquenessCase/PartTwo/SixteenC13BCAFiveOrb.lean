module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAFiveOmEq
import CFSG.RankThree.GF2n.Smith81.Lin31TwoAlg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.Quasithin.G11.P3Ortho.Om4

private theorem s16c13bcA_sl2_vec_e0 {K : Type} [Field K] {x : Fin 2 → K} (hx : x ≠ 0) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) K,
      (A : Matrix (Fin 2) (Fin 2) K) *ᵥ (![1, 0] : Fin 2 → K) = x := by
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := by
      intro h1
      apply hx
      funext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨⟨!![0, -(x 1)⁻¹; x 1, 0], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one]
      rw [zero_mul, zero_sub, neg_mul, neg_neg, inv_mul_cancel₀ h1]
    · funext i
      fin_cases i <;>
        rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two] <;>
        simp [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_succ,
          Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one, h0]
  · refine ⟨⟨!![x 0, 0; x 1, (x 0)⁻¹], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one]
      rw [zero_mul, sub_zero, mul_inv_cancel₀ h0]
    · funext i
      fin_cases i <;>
        rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two] <;>
        simp [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_succ,
          Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one]

private theorem s16c13bcA_sl2_vec_transitive {K : Type} [Field K]
    {x y : Fin 2 → K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) K,
      (A : Matrix (Fin 2) (Fin 2) K) *ᵥ x = y := by
  obtain ⟨Ax, hAx⟩ := s16c13bcA_sl2_vec_e0 hx
  obtain ⟨Ay, hAy⟩ := s16c13bcA_sl2_vec_e0 hy
  refine ⟨Ay * Ax⁻¹, ?_⟩
  have hinv : ((Ax⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) *ᵥ x = (![1, 0] : Fin 2 → K) := by
    rw [← hAx, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hinv, hAy]

private theorem s16c13bcA_det_eq_zero_of_odd_orbit {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) {v : Fin 2 ⊕ Fin 2 → K} (hv : v ≠ 0)
    (o : Odd (Nat.card (MulAction.orbit ↥(StatedOmega (StatedQuadPlus 2 K)) v))) :
    (toMat K v).det = 0 := by
  classical
  let Ω := ↥(StatedOmega (StatedQuadPlus 2 K))
  obtain ⟨ε, hε⟩ := s16c13bcA_omega_equiv_apply (K := K) hK.ge
  haveI : Fintype Ω := Fintype.ofFinite Ω
  haveI : Fintype (MulAction.orbit Ω v) := Fintype.ofFinite _
  haveI : Fintype (MulAction.stabilizer Ω v) := Fintype.ofFinite _
  by_contra hdet
  have hunit : IsUnit (toMat K v) :=
    (Matrix.isUnit_iff_isUnit_det (toMat K v)).mpr (isUnit_iff_ne_zero.mpr hdet)
  let s : MulAction.stabilizer Ω v →* Matrix.SpecialLinearGroup (Fin 2) K :=
    (MonoidHom.fst _ _).comp (ε.toMonoidHom.comp (MulAction.stabilizer Ω v).subtype)
  have hs : Function.Injective s := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    change (ε γ.1).1 = 1 at hγ
    have hfix : ((γ.1 : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v = v :=
      MulAction.mem_stabilizer_iff.mp γ.2
    have hεγ := hε γ.1 v
    rw [hfix, hγ, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul] at hεγ
    have h2m : (((ε γ.1).2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = 1 := by
      refine hunit.mul_left_cancel ?_
      rw [Matrix.mul_one]
      exact hεγ.symm
    have h2 : ((ε γ.1).2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) = 1 := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      simpa [Matrix.SpecialLinearGroup.coe_one] using congrFun (congrFun h2m i) j
    have hε1 : ε γ.1 = 1 := by
      rw [Prod.ext_iff]
      exact ⟨hγ, inv_eq_one.mp h2⟩
    have hγ1 : γ.1 = 1 := by
      have hε1' : ε γ.1 = ε 1 := by rw [hε1, map_one]
      exact ε.injective hε1'
    exact Subtype.ext hγ1
  have hdvd : Nat.card (MulAction.stabilizer Ω v) ∣ 60 := by
    have h := Subgroup.card_dvd_of_injective s hs
    rwa [s16c13bcA_card_sl2_four hK] at h
  obtain ⟨t, ht⟩ := hdvd
  have hOS : Nat.card (MulAction.orbit Ω v) * Nat.card (MulAction.stabilizer Ω v) = 3600 := by
    rw [Nat.card_eq_fintype_card (α := MulAction.orbit Ω v),
      Nat.card_eq_fintype_card (α := MulAction.stabilizer Ω v),
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := Ω) v,
      ← Nat.card_eq_fintype_card (α := Ω)]
    exact s16c13bcA_card_omega_four hK
  have ha60 : Nat.card (MulAction.orbit Ω v) * 60 = 3600 * t := by
    rw [ht, ← mul_assoc, hOS]
  have ha : Nat.card (MulAction.orbit Ω v) = 60 * t := by
    refine Nat.mul_right_cancel (m := 60) (by norm_num) ?_
    rw [ha60]
    ring
  have heven : Even (Nat.card (MulAction.orbit Ω v)) := by
    refine ⟨30 * t, ?_⟩
    rw [ha]
    ring
  exact (Nat.not_odd_iff_even.mpr heven) o

theorem s16c13bcA_omega_orbit_unique {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) {v₁ v₂ : Fin 2 ⊕ Fin 2 → K} (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0)
    (o₁ : Odd (Nat.card (MulAction.orbit ↥(StatedOmega (StatedQuadPlus 2 K)) v₁)))
    (o₂ : Odd (Nat.card (MulAction.orbit ↥(StatedOmega (StatedQuadPlus 2 K)) v₂))) :
    v₂ ∈ MulAction.orbit ↥(StatedOmega (StatedQuadPlus 2 K)) v₁ := by
  classical
  let Ω := ↥(StatedOmega (StatedQuadPlus 2 K))
  obtain ⟨ε, hε⟩ := s16c13bcA_omega_equiv_apply (K := K) hK.ge
  have hdet₁ : (toMat K v₁).det = 0 := s16c13bcA_det_eq_zero_of_odd_orbit hK h₁ o₁
  have hdet₂ : (toMat K v₂).det = 0 := s16c13bcA_det_eq_zero_of_odd_orbit hK h₂ o₂
  have hX₁ : toMat K v₁ ≠ 0 := fun h => h₁ ((toMat K).map_eq_zero_iff.mp h)
  have hX₂ : toMat K v₂ ≠ 0 := fun h => h₂ ((toMat K).map_eq_zero_iff.mp h)
  obtain ⟨n₁, u₁, hn₁, hu₁, hv₁⟩ :=
    CFSG.RankThree.GF2n.Smith81.exists_vecMulVec_of_det_eq_zero hX₁ hdet₁
  obtain ⟨n₂, u₂, hn₂, hu₂, hv₂⟩ :=
    CFSG.RankThree.GF2n.Smith81.exists_vecMulVec_of_det_eq_zero hX₂ hdet₂
  obtain ⟨A, hA⟩ := s16c13bcA_sl2_vec_transitive hn₁ hn₂
  obtain ⟨C, hC⟩ := s16c13bcA_sl2_vec_transitive hu₁ hu₂
  let B : Matrix.SpecialLinearGroup (Fin 2) K := (Matrix.SpecialLinearGroup.transpose C)⁻¹
  have hBinv : ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = (C : Matrix (Fin 2) (Fin 2) K).transpose := by
    have h : B⁻¹ = Matrix.SpecialLinearGroup.transpose C := by simp [B]
    rw [h, Matrix.SpecialLinearGroup.coe_transpose]
  let γ : Ω := ε.symm (A, B)
  have hmat : (A : Matrix (Fin 2) (Fin 2) K) * toMat K v₁ *
      ((B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      toMat K v₂ := by
    rw [hv₁, hv₂, hBinv]
    calc (A : Matrix (Fin 2) (Fin 2) K) * Matrix.vecMulVec n₁ u₁ *
          (C : Matrix (Fin 2) (Fin 2) K).transpose
        = Matrix.vecMulVec ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ n₁) u₁ *
            (C : Matrix (Fin 2) (Fin 2) K).transpose := by rw [Matrix.mul_vecMulVec]
      _ = Matrix.vecMulVec ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ n₁)
            (u₁ ᵥ* (C : Matrix (Fin 2) (Fin 2) K).transpose) := by rw [Matrix.vecMulVec_mul]
      _ = Matrix.vecMulVec n₂ ((C : Matrix (Fin 2) (Fin 2) K) *ᵥ u₁) := by
            rw [hA, Matrix.vecMul_transpose]
      _ = Matrix.vecMulVec n₂ u₂ := by rw [hC]
  have htoMat : toMat K (γ • v₁) = toMat K v₂ := by
    have h := hε γ v₁
    rw [show ε γ = (A, B) from ε.apply_symm_apply (A, B)] at h
    simp only [Prod.fst, Prod.snd] at h
    exact h.trans hmat
  have hγv : γ • v₁ = v₂ := (toMat K).injective htoMat
  exact MulAction.mem_orbit_iff.mpr ⟨γ, hγv⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
