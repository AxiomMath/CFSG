module

public import CFSG.RankThree.Classical2.MatrixFrobeniusLang
public import CFSG.RankThree.Classical2.SLnSemilinearRigidity
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedTools

public section

namespace CFSG.RankThree.UnitaryBlock

open Matrix CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (blockSL coe_blockSL coe_blockGL_eq_diagBlock
  diagBlock diagBlock_map diagBlock_mul diagBlock_transpose diagBlock_one)
open scoped MatrixGroups

theorem map_blockSL {K L : Type*} [Field K] [Field L] (φ : K →+* L) {a m : ℕ}
    (Y : SpecialLinearGroup (Fin a) K) :
    SpecialLinearGroup.map φ (blockSL K a m Y) = blockSL L a m (SpecialLinearGroup.map φ Y) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, coe_blockSL, coe_blockSL, coe_blockGL_eq_diagBlock,
    coe_blockGL_eq_diagBlock, SpecialLinearGroup.coe_GL_coe_matrix,
    SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, diagBlock, diagBlock, reindex_apply,
    reindex_apply, ← submatrix_map, fromBlocks_map, Matrix.map_zero _ (map_zero φ),
    Matrix.map_zero _ (map_zero φ), Matrix.map_one _ (map_zero φ) (map_one φ)]

theorem transpose_mul_mul_eq_det_smul {R : Type*} [CommRing R] (X : Matrix (Fin 2) (Fin 2) R) :
    Xᵀ * !![0, 1; -1, 0] * X = X.det • !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

variable {ℓ f : ℕ} {k : Type*} [Field k] {Ω : Type*} [Field Ω] [Algebra k Ω]

theorem exists_blockSL_conj_mem_unitarySet (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hk : Nat.card k = ℓ ^ f) [IsAlgClosure k Ω] :
    ∃ C : SL(2, Ω), ∀ (m : ℕ) (Y : SL(2, k)), SpecialLinearGroup.toGL (blockSL Ω 2 m
      (C⁻¹ * SpecialLinearGroup.map (algebraMap k Ω) Y * C)) ∈ unitarySet (ℓ ^ f) (2 + m) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype k := Fintype.ofFinite k
  have : CharP k ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap k Ω).injective ℓ
  set σ : Ω →+* Ω := iterateFrobenius Ω ℓ f with hσdef
  have hσ' : ∀ c, σ c = c ^ ℓ ^ f := fun c => iterateFrobenius_def ℓ f c
  have hσfun : (fun c : Ω => c ^ ℓ ^ f) = ⇑σ := funext fun c => (hσ' c).symm
  set Jm : Matrix (Fin 2) (Fin 2) Ω := !![0, 1; -1, 0] with hJm
  set Ji : Matrix (Fin 2) (Fin 2) Ω := !![0, -1; 1, 0] with hJi
  have hJJi : Jm * Ji = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Jm, Ji, Matrix.mul_apply, Fin.sum_univ_two]
  have hJiJ : Ji * Jm = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Jm, Ji, Matrix.mul_apply, Fin.sum_univ_two]
  have hJJ : Jm * Jm = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Jm, Matrix.mul_apply, Fin.sum_univ_two]
  have hJiJi : Ji * Ji = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Ji, Matrix.mul_apply, Fin.sum_univ_two]
  have hJt : Jmᵀ = Ji := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Jm, Ji]
  have hJit : Jiᵀ = Jm := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Jm, Ji]
  have hσJ : Jm.map σ = Jm := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Jm]
  have hσJi : Ji.map σ = Ji := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Ji]
  obtain ⟨H₂, hH₂det, hH₂⟩ := (matrix_frobenius_lang hℓ hf hk (by norm_num : 1 ≤ 2)
    (GeneralLinearGroup.mkOfDetNeZero Jm (by simp [Jm, Matrix.det_fin_two]))).2
      (by simp [Jm, Matrix.det_fin_two])
  set C : SL(2, Ω) := ⟨(H₂ : Matrix (Fin 2) (Fin 2) Ω), hH₂det⟩ with hCdef
  set h : Matrix (Fin 2) (Fin 2) Ω := (H₂ : Matrix (Fin 2) (Fin 2) Ω) with hhdef
  set hi : Matrix (Fin 2) (Fin 2) Ω := ((C⁻¹ : SL(2, Ω)) : Matrix (Fin 2) (Fin 2) Ω) with hhidef
  have hhi : h * hi = 1 := congrArg Subtype.val (mul_inv_cancel C)
  have hih : hi * h = 1 := congrArg Subtype.val (inv_mul_cancel C)
  have hGinv : (↑H₂⁻¹ : Matrix (Fin 2) (Fin 2) Ω) = hi := by
    calc (↑H₂⁻¹ : Matrix (Fin 2) (Fin 2) Ω) = ↑H₂⁻¹ * (h * hi) := by rw [hhi, Matrix.mul_one]
      _ = (↑H₂⁻¹ * h) * hi := by rw [Matrix.mul_assoc]
      _ = hi := by rw [hhdef, Units.inv_mul, Matrix.one_mul]
  have hσh : h.map σ = h * Jm := by
    have h1 : Jm = hi * h.map σ := by
      rw [← hσfun, ← hGinv]
      exact hH₂
    rw [h1, ← Matrix.mul_assoc, hhi, Matrix.one_mul]
  have hσhi : hi.map σ = Ji * hi := by
    have h1 : hi.map σ * h.map σ = 1 := by
      rw [← Matrix.map_mul, hih, Matrix.map_one _ (map_zero σ) (map_one σ)]
    calc hi.map σ = hi.map σ * (h.map σ * (Ji * hi)) := by
          rw [hσh, Matrix.mul_assoc, ← Matrix.mul_assoc Jm, hJJi, Matrix.one_mul, hhi,
            Matrix.mul_one]
      _ = Ji * hi := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine ⟨C, fun m Y => ?_⟩
  set X : Matrix (Fin 2) (Fin 2) Ω :=
    ((C⁻¹ * SpecialLinearGroup.map (algebraMap k Ω) Y * C : SL(2, Ω)) :
      Matrix (Fin 2) (Fin 2) Ω) with hXdef
  have hXdet : X.det = 1 := (C⁻¹ * SpecialLinearGroup.map (algebraMap k Ω) Y * C).2
  have hy : ((SpecialLinearGroup.map (algebraMap k Ω) Y : SL(2, Ω)) :
      Matrix (Fin 2) (Fin 2) Ω).map σ =
        ((SpecialLinearGroup.map (algebraMap k Ω) Y : SL(2, Ω)) : Matrix (Fin 2) (Fin 2) Ω) := by
    ext i j
    rw [Matrix.map_apply, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, hσ', ← map_pow, ← hk, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hσX : X.map σ = Ji * X * Jm := by
    rw [hXdef, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.map_mul, Matrix.map_mul, hy]
    change hi.map σ * _ * h.map σ = _
    rw [hσhi, hσh]
    simp only [Matrix.mul_assoc]
    rfl
  have hU : (X.map σ)ᵀ * X = 1 := by
    rw [hσX, Matrix.transpose_mul, Matrix.transpose_mul, hJt, hJit, Matrix.mul_assoc,
      Matrix.mul_assoc, ← Matrix.mul_assoc Xᵀ,
      show Xᵀ * Jm * X = X.det • Jm from transpose_mul_mul_eq_det_smul X, hXdet, one_smul, hJiJ]
  have hσσX : (X.map σ).map σ = X := by
    rw [hσX, Matrix.map_mul, Matrix.map_mul, hσX, hσJ, hσJi]
    calc Ji * (Ji * X * Jm) * Jm = (Ji * Ji) * X * (Jm * Jm) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [hJiJi, hJJ]; simp
  have hD1 : (1 : Matrix (Fin m) (Fin m) Ω).map σ = 1 :=
    Matrix.map_one _ (map_zero σ) (map_one σ)
  refine ⟨fun i j => ?_, ?_, ?_⟩
  · change (diagBlock X (1 : Matrix (Fin m) (Fin m) Ω)) i j ^ (ℓ ^ f) ^ 2 =
      (diagBlock X (1 : Matrix (Fin m) (Fin m) Ω)) i j
    have h2 : ((diagBlock X (1 : Matrix (Fin m) (Fin m) Ω)).map σ).map σ = diagBlock X 1 := by
      rw [diagBlock_map, diagBlock_map, hσσX, hD1, hD1]
    have h3 := congrFun (congrFun h2 i) j
    rw [Matrix.map_apply, Matrix.map_apply, hσ', hσ', ← pow_mul, ← pow_two] at h3
    exact h3
  · exact (blockSL Ω 2 m (C⁻¹ * SpecialLinearGroup.map (algebraMap k Ω) Y * C)).2
  · change ((diagBlock X (1 : Matrix (Fin m) (Fin m) Ω)).map (· ^ ℓ ^ f))ᵀ *
      diagBlock X (1 : Matrix (Fin m) (Fin m) Ω) = 1
    rw [hσfun, diagBlock_map, hD1, diagBlock_transpose, transpose_one, diagBlock_mul, hU,
      Matrix.mul_one, diagBlock_one]

end CFSG.RankThree.UnitaryBlock
