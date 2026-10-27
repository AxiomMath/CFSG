module

public import CFSG.RankThree.PartOne.N1322.CoreDefs
public import CFSG.RankThree.SubgroupLists.SchurCommutant
public import CFSG.RankThree.PartOne.KF.BloomOmega

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartOne.KF1322

open Matrix CFSG.RankThree.SubgroupLists CFSG.RankThree.PartOne.LIT CFSG.RepresentationTheory

section Generic

variable {σ K : Type*} [Field K] [Fintype σ] [DecidableEq σ]

theorem commute_inv_mul_of_forms {M M' : Matrix σ σ K} (hdet : M.det ≠ 0) {h : GL σ K}
    (hM : (h : Matrix σ σ K)ᵀ * M * (h : Matrix σ σ K) = M)
    (hM' : (h : Matrix σ σ K)ᵀ * M' * (h : Matrix σ σ K) = M') :
    (h : Matrix σ σ K) * (M⁻¹ * M') = (M⁻¹ * M') * (h : Matrix σ σ K) := by
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  set H : Matrix σ σ K := (h : Matrix σ σ K) with hH
  set Hi : Matrix σ σ K := ((h⁻¹ : GL σ K) : Matrix σ σ K) with hHi
  have hHHi : H * Hi = 1 := by rw [hH, hHi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hHiH : Hi * H = 1 := by rw [hH, hHi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hHit : Hiᵀ * Hᵀ = 1 := by rw [← Matrix.transpose_mul, hHHi, Matrix.transpose_one]
  have hNM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hu
  have hMN : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hu
  have s1 : M * H = Hiᵀ * M := by
    calc M * H = (Hiᵀ * Hᵀ) * M * H := by rw [hHit, Matrix.one_mul]
      _ = Hiᵀ * (Hᵀ * M * H) := by simp only [Matrix.mul_assoc]
      _ = Hiᵀ * M := by rw [hM]
  have s2 : M' * H = Hiᵀ * M' := by
    calc M' * H = (Hiᵀ * Hᵀ) * M' * H := by rw [hHit, Matrix.one_mul]
      _ = Hiᵀ * (Hᵀ * M' * H) := by simp only [Matrix.mul_assoc]
      _ = Hiᵀ * M' := by rw [hM']
  have s3 : H * M⁻¹ = M⁻¹ * Hiᵀ := by
    calc H * M⁻¹ = M⁻¹ * (M * H) * M⁻¹ := by
          rw [← Matrix.mul_assoc, hNM, Matrix.one_mul]
      _ = M⁻¹ * (Hiᵀ * M) * M⁻¹ := by rw [s1]
      _ = M⁻¹ * Hiᵀ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hMN, Matrix.mul_one]
  calc H * (M⁻¹ * M') = (H * M⁻¹) * M' := by rw [Matrix.mul_assoc]
    _ = (M⁻¹ * Hiᵀ) * M' := by rw [s3]
    _ = M⁻¹ * (Hiᵀ * M') := by rw [Matrix.mul_assoc]
    _ = M⁻¹ * (M' * H) := by rw [s2]
    _ = (M⁻¹ * M') * H := by rw [Matrix.mul_assoc]

end Generic

theorem omegaGL_commutant_scalar {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hdet : M.det ≠ 0)
    (hirr : IsIrreducibleMatrixRep (omegaGL M).subtype) (S : Matrix (Fin 3) (Fin 3) (ZMod p))
    (hS : ∀ g ∈ omegaGL M, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * S = S * g) :
    ∃ c : ZMod p, S = Matrix.scalar (Fin 3) c := by
  rcases scalar_commutant_or_cyclic Nat.prime_three hirr with hs | ⟨hcyc, -, hnd⟩
  · exact hs S hS
  · exfalso
    have : IsMulCommutative (omegaGL M) := hcyc.isMulCommutative
    have : Group.IsPerfect (omegaGL M) := KFBloom.omegaGL_isPerfect hp M hMt hdet
    have hbot : omegaGL M = ⊥ := Subgroup.eq_bot_of_subsingleton _
    have h1 : Nat.card (omegaGL M) = 1 := Subgroup.card_eq_one.mpr hbot
    rw [h1] at hnd
    exact hnd (one_dvd _)

theorem det_refl {K : Type*} [Field K] {t : GL (Fin 3) K} (ht : N1322.IsRefl t) :
    (t : Matrix (Fin 3) (Fin 3) K).det = -1 := by
  obtain ⟨r, φ, hr, hφ, hg⟩ := ht
  have h : (1 - vecMulVec r φ : Matrix (Fin 3) (Fin 3) K) =
      1 + replicateCol (Fin 1) r * replicateRow (Fin 1) (-φ) := by
    ext i j
    simp [vecMulVec_apply, Matrix.mul_apply, sub_eq_add_neg]
  have h3 := Matrix.det_one_add_mul_comm (replicateCol (Fin 1) r) (replicateRow (Fin 1) (-φ))
  rw [hg, h, h3, Matrix.det_fin_one]
  simp [Matrix.mul_apply, Fin.sum_univ_three]
  have : φ 0 * r 0 + φ 1 * r 1 + φ 2 * r 2 = 2 := by
    simpa [dotProduct, Fin.sum_univ_three] using hφ
  linear_combination -this

theorem refl_isometry {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hdet : M.det ≠ 0)
    (hirr : IsIrreducibleMatrixRep (omegaGL M).subtype)
    {t : GL (Fin 3) (ZMod p)} (ht : N1322.IsRefl t)
    (hnorm : ∀ x ∈ omegaGL M, t * x * t⁻¹ ∈ omegaGL M) :
    (t : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M * (t : Matrix (Fin 3) (Fin 3) (ZMod p)) = M := by
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin 3) (Fin 3) (ZMod p), T = (t : Matrix (Fin 3) (Fin 3) (ZMod p)) :=
    ⟨_, rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M' : Matrix (Fin 3) (Fin 3) (ZMod p), M' = Tᵀ * M * T := ⟨_, rfl⟩
  rw [← hT]
  have htt : T * T = 1 := by
    have := congrArg (fun x : GL (Fin 3) (ZMod p) => (x : Matrix (Fin 3) (Fin 3) (ZMod p))) ht.sq
    simpa [hT] using this
  have hTt : Tᵀ * Tᵀ = 1 := by rw [← Matrix.transpose_mul, htt, Matrix.transpose_one]
  have hscal : ∃ c : ZMod p, M⁻¹ * M' = Matrix.scalar (Fin 3) c := by
    refine omegaGL_commutant_scalar hp hMt hdet hirr _ fun g hg => ?_
    have hgso : g ∈ soGL M := omegaGL_le_soGL M hg
    have hg' : g ∈ soGL M' := by
      rw [hM', hT]
      exact (mem_soGL_congr t M g).mpr (omegaGL_le_soGL M (hnorm g hg))
    exact commute_inv_mul_of_forms hdet hgso.1 hg'.1
  obtain ⟨c, hc⟩ := hscal
  have hM'c : M' = c • M := by
    have : M * (M⁻¹ * M') = M' := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hdet),
        Matrix.one_mul]
    rw [← this, hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
      Matrix.mul_one]
  have hdetT : T.det = -1 := by rw [hT]; exact det_refl ht
  have h3 : c ^ 3 = 1 := by
    have h1 : M'.det = M.det := by
      rw [hM', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetT]
      norm_num
    rw [hM'c, Matrix.det_smul, Fintype.card_fin] at h1
    exact mul_right_cancel₀ hdet (by rw [one_mul]; exact h1)
  have h2 : c ^ 2 = 1 := by
    have e : M = Tᵀ * M' * T := by
      calc M = (Tᵀ * Tᵀ) * M * (T * T) := by rw [hTt, htt, Matrix.one_mul, Matrix.mul_one]
        _ = Tᵀ * (Tᵀ * M * T) * T := by simp only [Matrix.mul_assoc]
        _ = Tᵀ * M' * T := by rw [hM']
    have : c ^ 2 • M = (1 : ZMod p) • M := by
      rw [one_smul]
      conv_rhs => rw [e, hM'c, Matrix.mul_smul, Matrix.smul_mul, ← hM', hM'c, smul_smul, ← pow_two]
    have hM0 : M ≠ 0 := by
      intro h0
      apply hdet
      rw [h0]
      simp
    obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hM0 (by ext i j; exact hcon i j)
    have h4 := congrFun (congrFun this i) j
    simp only [Matrix.smul_apply, smul_eq_mul, one_mul] at h4
    exact mul_right_cancel₀ hij (by rw [one_mul]; exact h4)
  have hc1 : c = 1 := by linear_combination h3 - c * h2
  rw [hc1, one_smul] at hM'c
  rw [← hM', hM'c]

theorem dot_mulVec_isometry {K : Type*} [Field K] {M T : Matrix (Fin 3) (Fin 3) K}
    (h : Tᵀ * M * T = M) (u v : Fin 3 → K) :
    (T *ᵥ u) ⬝ᵥ (M *ᵥ (T *ᵥ v)) = u ⬝ᵥ (M *ᵥ v) := by
  have e1 : (T *ᵥ u) ⬝ᵥ (M *ᵥ (T *ᵥ v)) = u ⬝ᵥ (Tᵀ *ᵥ (M *ᵥ (T *ᵥ v))) := by
    rw [← Matrix.vecMul_transpose T u, ← Matrix.dotProduct_mulVec]
  rw [e1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem refl_geom {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {M : Matrix (Fin 3) (Fin 3) K} (hMt : Mᵀ = M) (hdet : M.det ≠ 0)
    {T : Matrix (Fin 3) (Fin 3) K} (hiso : Tᵀ * M * T = M)
    {r φ : Fin 3 → K} (hr : r ≠ 0) (hφ : φ ⬝ᵥ r = 2) (hTm : T = 1 - vecMulVec r φ) :
    r ⬝ᵥ (M *ᵥ r) ≠ 0 ∧ T *ᵥ r = -r ∧ ∀ v, r ⬝ᵥ (M *ᵥ v) = 0 → T *ᵥ v = v := by
  have hTv : ∀ v, T *ᵥ v = v - (φ ⬝ᵥ v) • r := by
    intro v
    rw [hTm, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
    simp
  have hTr : T *ᵥ r = -r := by
    rw [hTv, hφ]
    simp [two_smul]
  have hkey : ∀ v, (φ ⬝ᵥ v) * (r ⬝ᵥ (M *ᵥ r)) = 2 * (r ⬝ᵥ (M *ᵥ v)) := by
    intro v
    have h1 := dot_mulVec_isometry hiso r v
    rw [hTr, hTv v, Matrix.mulVec_sub, Matrix.mulVec_smul, neg_dotProduct, dotProduct_sub,
      dotProduct_smul, smul_eq_mul] at h1
    linear_combination h1
  have ha : r ⬝ᵥ (M *ᵥ r) ≠ 0 := by
    intro ha
    have h0 : ∀ v, r ⬝ᵥ (M *ᵥ v) = 0 := by
      intro v
      have := hkey v
      rw [ha, mul_zero] at this
      exact (mul_eq_zero.mp this.symm).resolve_left h2
    have hMr : M *ᵥ r = 0 := by
      apply dotProduct_eq_zero_iff.mp
      intro w
      have : r ⬝ᵥ (M *ᵥ w) = (M *ᵥ r) ⬝ᵥ w := by
        rw [Matrix.dotProduct_mulVec]
        have := Matrix.vecMul_transpose M r
        rw [hMt] at this
        rw [this]
      rw [← this]
      exact h0 w
    exact hr (Matrix.eq_zero_of_mulVec_eq_zero hdet hMr)
  refine ⟨ha, hTr, fun v hv => ?_⟩
  have h3 := hkey v
  rw [hv, mul_zero] at h3
  have h4 : φ ⬝ᵥ v = 0 := (mul_eq_zero.mp h3).resolve_right ha
  rw [hTv, h4, zero_smul, sub_zero]

end CFSG.RankThree.PartOne.KF1322
