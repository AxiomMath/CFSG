module

public import Mathlib.LinearAlgebra.Eigenspace.Semisimple

public section

namespace CFSG.RankThree.PartTwo.Sec8.ReeF4Conj2Proof

open Matrix Polynomial Module
open scoped MatrixGroups

variable {L : Type*} [Field L] [IsAlgClosed L]

theorem exists_basis_eigen (f : Module.End L (Fin 3 → L)) (hf : f.IsSemisimple) :
    ∃ (b : Basis (Fin 3) L (Fin 3 → L)) (μ : Fin 3 → L), ∀ k, f (b k) = μ k • b k := by
  classical
  have htop := hf.iSup_eigenspace_eq_top
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    f.eigenspaces_iSupIndep htop
  let v : ∀ μ, Basis _ L (f.eigenspace μ) := fun μ => Basis.ofVectorSpace L _
  let B := hint.collectedBasis v
  let e := B.indexEquiv (Pi.basisFun L (Fin 3))
  refine ⟨B.reindex e, fun k => (e.symm k).1, fun k => ?_⟩
  rw [Basis.reindex_apply]
  have hmem := hint.collectedBasis_mem v (e.symm k)
  exact Module.End.mem_eigenspace_iff.1 hmem

theorem exists_conj_diag (h3 : (3 : L) ≠ 0) (M : SL(3, L)) (hM : M ^ 3 = 1) :
    ∃ P D : SL(3, L), (∀ i j : Fin 3, i ≠ j → (D : Matrix (Fin 3) (Fin 3) L) i j = 0) ∧
      M = P * D * P⁻¹ := by
  classical
  set A : Matrix (Fin 3) (Fin 3) L := (M : Matrix (Fin 3) (Fin 3) L) with hA
  have hA3 : A ^ 3 = 1 := by
    have := congrArg (fun X : SL(3, L) => (X : Matrix (Fin 3) (Fin 3) L)) hM
    simpa [hA] using this
  set f : Module.End L (Fin 3 → L) := Matrix.toLinAlgEquiv' A with hf
  have hsq : Squarefree (X ^ 3 - C (1 : L)) :=
    (separable_X_pow_sub_C (1 : L) (by exact_mod_cast h3) one_ne_zero).squarefree
  have hev : aeval f (X ^ 3 - C (1 : L)) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_one]
    rw [hf, ← map_pow, hA3, map_one, sub_self]
  obtain ⟨b, μ, hb⟩ := exists_basis_eigen f
    (Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq hev)
  set P0 : Matrix (Fin 3) (Fin 3) L := (Pi.basisFun L (Fin 3)).toMatrix b with hP0
  set Q0 : Matrix (Fin 3) (Fin 3) L := b.toMatrix (Pi.basisFun L (Fin 3)) with hQ0
  have hPQ : P0 * Q0 = 1 := Basis.toMatrix_mul_toMatrix_flip _ _
  have hQP : Q0 * P0 = 1 := Basis.toMatrix_mul_toMatrix_flip _ _
  have hcol : ∀ i k, P0 i k = b k i := fun i k => by
    rw [hP0, Basis.toMatrix_apply, Pi.basisFun_repr]
  have hAP : A * P0 = P0 * Matrix.diagonal μ := by
    ext i k
    rw [Matrix.mul_diagonal, hcol]
    have h1 := congrFun (hb k) i
    rw [hf, Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, Pi.smul_apply, smul_eq_mul] at h1
    rw [Matrix.mul_apply, mul_comm (b k i), ← h1]
    simp only [dotProduct, hcol]
  have hAeq : A = P0 * Matrix.diagonal μ * Q0 := by
    rw [← hAP, Matrix.mul_assoc, hPQ, Matrix.mul_one]
  have hdP : P0.det * Q0.det = 1 := by rw [← Matrix.det_mul, hPQ, Matrix.det_one]
  have hdP0 : P0.det ≠ 0 := left_ne_zero_of_mul_eq_one hdP
  have hdetA : A.det = 1 := M.2
  have hdD : (Matrix.diagonal μ).det = 1 := by
    have h := congrArg Matrix.det hAeq
    rw [Matrix.det_mul, Matrix.det_mul, hdetA, mul_comm P0.det, mul_assoc, hdP, mul_one] at h
    exact h.symm
  set d : L := P0.det with hd
  set c : Matrix (Fin 3) (Fin 3) L := Matrix.diagonal ![d⁻¹, 1, 1] with hc
  set c' : Matrix (Fin 3) (Fin 3) L := Matrix.diagonal ![d, 1, 1] with hc'
  have hc'c : c' * c = 1 := by
    rw [hc, hc', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hdP0]
  have hdetc : c.det = d⁻¹ := by
    rw [hc, Matrix.det_diagonal, Fin.prod_univ_three]
    simp
  set P : Matrix (Fin 3) (Fin 3) L := P0 * c with hP
  have hdetP : P.det = 1 := by rw [hP, Matrix.det_mul, hdetc, ← hd, mul_inv_cancel₀ hdP0]
  let P' : SL(3, L) := ⟨P, hdetP⟩
  let D' : SL(3, L) := ⟨Matrix.diagonal μ, hdD⟩
  refine ⟨P', D', fun i j hij => Matrix.diagonal_apply_ne μ hij, ?_⟩
  apply Subtype.ext
  have hinv : ((P'⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = c' * Q0 := by
    have h1 : P * ((P'⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = 1 := by
      have := congrArg (fun X : SL(3, L) => (X : Matrix (Fin 3) (Fin 3) L)) (mul_inv_cancel P')
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at this
      exact this
    have h2 : (c' * Q0) * P = 1 := by
      rw [hP, Matrix.mul_assoc, ← Matrix.mul_assoc Q0, hQP, Matrix.one_mul, hc'c]
    calc ((P'⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
        ((c' * Q0) * P) * ((P'⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) := by
          rw [h2, Matrix.one_mul]
      _ = c' * Q0 := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have hcomm : c * Matrix.diagonal μ * c' = Matrix.diagonal μ := by
    rw [hc, hc', Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      field_simp
    · simp
    · simp
  change A = P * Matrix.diagonal μ * ((P'⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L)
  rw [hinv, hAeq, hP]
  calc P0 * Matrix.diagonal μ * Q0 = P0 * (c * Matrix.diagonal μ * c') * Q0 := by rw [hcomm]
    _ = P0 * c * Matrix.diagonal μ * (c' * Q0) := by simp only [Matrix.mul_assoc]

end CFSG.RankThree.PartTwo.Sec8.ReeF4Conj2Proof
