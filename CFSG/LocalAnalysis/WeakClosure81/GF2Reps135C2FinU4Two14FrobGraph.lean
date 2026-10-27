module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinU4Two14Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped MatrixGroups Matrix
open CFSG.HardMathSupport.U4FF (SU4 twistHom)
open CFSG.LieType.Universal.Unitary (antidiag conjTr mem_SU)
open CFSG.LieType.BorelTits (unitaryInvolution_apply)

section Matrices

variable (k : Type) [Field k]

theorem antidiag_four_eq : (antidiag 4 : Matrix (Fin 4) (Fin 4) k) =
    !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antidiag, Fin.rev]

theorem antidiag_four_transpose : (antidiag 4 : Matrix (Fin 4) (Fin 4) k)ᵀ = antidiag 4 := by
  rw [antidiag_four_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem antidiag_four_map {k' : Type} [Field k'] (φ : k →+* k') :
    (antidiag 4 : Matrix (Fin 4) (Fin 4) k).map φ = antidiag 4 := by
  ext i j
  simp only [Matrix.map_apply, antidiag, Matrix.of_apply]
  split_ifs <;> simp

theorem finU4ZMat_det : (finU4ZMat k).det = 1 := by
  simp [finU4ZMat, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

theorem finU4ZMat_map {k' : Type} [Field k'] (φ : k →+* k') :
    (finU4ZMat k).map φ = finU4ZMat k' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [finU4ZMat]

theorem finU4ZMat_mul_self [CharP k 2] : finU4ZMat k * finU4ZMat k = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finU4ZMat, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero]

@[expose] def finU4J [CharP k 2] : SL(4, k) :=
  ⟨antidiag 4, CFSG.HardMathSupport.U4FF.det_antidiag⟩

@[expose] def finU4Z1 : SL(4, k) := ⟨finU4ZMat k, finU4ZMat_det k⟩

theorem finU4J_map {k' : Type} [Field k'] [CharP k 2] [CharP k' 2] (φ : k →+* k') :
    Matrix.SpecialLinearGroup.map φ (finU4J k) = finU4J k' :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    exact antidiag_four_map k φ)

theorem finU4Z1_map {k' : Type} [Field k'] (φ : k →+* k') :
    Matrix.SpecialLinearGroup.map φ (finU4Z1 k) = finU4Z1 k' :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    exact finU4ZMat_map k φ)

end Matrices

section Unitary

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [CharP E 2]

theorem su4_map_sq_eq (φ : K →+* E) (x : SU4 K 1) :
    ((twistHom 1 φ x : SL(4, E)) : Matrix (Fin 4) (Fin 4) E).map (fun c => c ^ 2) =
      antidiag 4 *
        (((twistHom 1 φ x)⁻¹ : SL(4, E)) : Matrix (Fin 4) (Fin 4) E)ᵀ * antidiag 4 := by
  obtain ⟨-, hform⟩ := mem_SU.mp x.2
  set A : Matrix (Fin 4) (Fin 4) K := ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hA
  set g := twistHom 1 φ x with hg
  have hG : ((g : SL(4, E)) : Matrix (Fin 4) (Fin 4) E) = A.map φ := rfl
  have hmul : ((g : SL(4, E)) : Matrix (Fin 4) (Fin 4) E) *
      ((g⁻¹ : SL(4, E)) : Matrix (Fin 4) (Fin 4) E) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h1 := congrArg (fun M => M.map φ) hform
  simp only [Matrix.map_mul, antidiag_four_map] at h1
  have hconj : (conjTr (CFSG.LieType.BorelTits.unitaryInvolution K 2 1) A).map φ =
      ((A.map φ).map (fun c => c ^ 2))ᵀ := by
    ext i j
    simp [conjTr, unitaryInvolution_apply, map_pow, frobenius_def]
  rw [hconj] at h1
  rw [hG] at hmul ⊢
  set G : Matrix (Fin 4) (Fin 4) E := A.map φ with hGdef
  set Gi : Matrix (Fin 4) (Fin 4) E := ((g⁻¹ : SL(4, E)) : Matrix (Fin 4) (Fin 4) E) with hGi
  have h2 : (G.map (fun c => c ^ 2))ᵀ * antidiag 4 = antidiag 4 * Gi := by
    have h := congrArg (fun M => M * Gi) h1
    simp only [Matrix.mul_assoc, hmul, Matrix.mul_one] at h
    exact h
  have h3 : (G.map (fun c => c ^ 2))ᵀ = antidiag 4 * Gi * antidiag 4 := by
    calc (G.map (fun c => c ^ 2))ᵀ = (G.map (fun c => c ^ 2))ᵀ * (antidiag 4 * antidiag 4) := by
          rw [CFSG.HardMathSupport.U4FF.J_mul_J, Matrix.mul_one]
      _ = ((G.map (fun c => c ^ 2))ᵀ * antidiag 4) * antidiag 4 := (Matrix.mul_assoc _ _ _).symm
      _ = antidiag 4 * Gi * antidiag 4 := by rw [h2]
  calc G.map (fun c => c ^ 2) = (G.map (fun c => c ^ 2))ᵀᵀ :=
        (Matrix.transpose_transpose _).symm
    _ = (antidiag 4 * Gi * antidiag 4)ᵀ := by rw [h3]
    _ = antidiag 4 * Giᵀ * antidiag 4 := by
        simp only [Matrix.transpose_mul, antidiag_four_transpose, Matrix.mul_assoc]

theorem twistHom_frobPair (φ : K →+* E) {Z : Matrix (Fin 4) (Fin 4) K} {x y : SU4 K 1}
    (h : FinU4FrobPair Z x y) :
    ((twistHom 1 φ y : SL(4, E)) : Matrix (Fin 4) (Fin 4) E) =
      Z.map φ * ((twistHom 1 φ x : SL(4, E)) : Matrix (Fin 4) (Fin 4) E).map (fun c => c ^ 2) *
        Z.map φ := by
  have h0 : ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Z * ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (fun c => c ^ 2) * Z := h
  have h' := congrArg (fun M => M.map φ) h0
  simp only [Matrix.map_mul] at h'
  have hcomm : (((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (fun c => c ^ 2)).map φ =
      (((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ).map (fun c => c ^ 2) := by
    ext i j
    simp [map_pow]
  rw [hcomm] at h'
  exact h'

theorem finU4FrobPair_conj (φ : K →+* E) {Z : Matrix (Fin 4) (Fin 4) K} {x y : SU4 K 1}
    (h : FinU4FrobPair Z x y) (hZ : Z.map φ * Z.map φ = 1) (W : SL(4, E))
    (hW : (W : Matrix (Fin 4) (Fin 4) E) = Z.map φ * antidiag 4) :
    twistHom 1 φ y * W = W * Matrix.SpecialLinearGroup.transpose (twistHom 1 φ x)⁻¹ := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_transpose, hW, twistHom_frobPair φ h, su4_map_sq_eq φ x]
  have hZJ : Z.map φ * (Z.map φ * antidiag 4) = antidiag 4 := by
    rw [← Matrix.mul_assoc, hZ, Matrix.one_mul]
  simp only [Matrix.mul_assoc, hZJ]
  rw [CFSG.HardMathSupport.U4FF.J_mul_J, Matrix.mul_one]

end Unitary

end CFSG.LocalAnalysis.WeakClosure81
