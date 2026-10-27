module

public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3Cyc
public import CFSG.LieType.Universal.Unitary.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

open Matrix CFSG.LieType.Universal.Unitary

section NormalForm

variable {F : Type} [Field F]

theorem det_sub_smul_one (M : Matrix (Fin 3) (Fin 3) F) (l : F) :
    (M - l • (1 : Matrix (Fin 3) (Fin 3) F)).det =
      M.det - l * sInv M + l ^ 2 * M.trace - l ^ 3 := by
  simp [Matrix.det_fin_three, Matrix.trace_fin_three, sInv, Matrix.one_apply]
  ring

theorem exists_eigenvec_of_cube (M : Matrix (Fin 3) (Fin 3) F) (hM3 : M * M * M = 1)
    (hdet : M.det = 1) (hns : ∀ c : F, M ≠ c • (1 : Matrix (Fin 3) (Fin 3) F)) (l : F)
    (hl : l ^ 3 = 1) : ∃ v : Fin 3 → F, v ≠ 0 ∧ M *ᵥ v = l • v := by
  obtain ⟨ht, hs⟩ := charpoly_cube_of_not_scalar M hM3 hdet hns
  have hd : (M - l • (1 : Matrix (Fin 3) (Fin 3) F)).det = 0 := by
    rw [det_sub_smul_one, hdet, ht, hs, hl]; ring
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  refine ⟨v, hv0, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
  exact hv

variable (σ : F ≃+* F)

theorem conjTr_conjTr (hσ : ∀ c : F, σ (σ c) = c) {n : ℕ} (A : Matrix (Fin n) (Fin n) F) :
    conjTr σ (conjTr σ A) = A := by
  ext i j
  simp [conjTr, hσ]

theorem conjTr_diagonal {n : ℕ} (d : Fin n → F) :
    conjTr σ (diagonal d) = diagonal (fun i => σ (d i)) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [conjTr]
  · simp [conjTr, diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h)]

theorem det_conjTr {n : ℕ} (A : Matrix (Fin n) (Fin n) F) :
    (conjTr σ A).det = σ A.det := by
  rw [conjTr, Matrix.det_transpose, RingEquiv.map_det]
  rfl

theorem exists_normalForm (hσ : ∀ c : F, σ (σ c) = c) {ω : F} (h3 : (3 : F) ≠ 0)
    (hω : ω ^ 2 + ω + 1 = 0) (hσω : σ ω = ω)
    (hnorm : ∀ c : F, σ c = c → c ≠ 0 → ∃ β : F, σ β * β = c)
    (S : Matrix (Fin 3) (Fin 3) F) (hS : conjTr σ S = S) (hSdet : S.det ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) F) (hM : conjTr σ M * S * M = S) (hM3 : M * M * M = 1)
    (hMdet : M.det = 1) (hMns : ∀ c : F, M ≠ c • (1 : Matrix (Fin 3) (Fin 3) F)) :
    ∃ B : Matrix (Fin 3) (Fin 3) F, B.det ≠ 0 ∧ conjTr σ B * S * B = antidiag 3 ∧
      M * B = B * diagonal ![ω, 1, ω ^ 2] := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω1 : ω ≠ 1 := fun h => h3 (by rw [h] at hω; linear_combination hω)
  have hω0 : ω ≠ 0 := fun h => by rw [h] at hω; simp at hω
  have hω2 : ω ^ 2 ≠ 1 := fun h => h3 (by
    linear_combination (-(ω - 2)) * hω + ((ω - 2) + 1) * h)
  have hωω : ω ≠ ω ^ 2 := fun h => hω1 (by
    have : ω * (ω - 1) = 0 := by linear_combination -h
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hω0)))
  have hσω2 : σ (ω ^ 2) = ω ^ 2 := by rw [map_pow, hσω]
  obtain ⟨v₀, hv₀0, hv₀⟩ := exists_eigenvec_of_cube M hM3 hMdet hMns ω hω3
  obtain ⟨v₁, hv₁0, hv₁⟩ := exists_eigenvec_of_cube M hM3 hMdet hMns 1 (one_pow 3)
  obtain ⟨v₂, hv₂0, hv₂⟩ := exists_eigenvec_of_cube M hM3 hMdet hMns (ω ^ 2)
    (by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow])
  set vs : Fin 3 → Fin 3 → F := ![v₀, v₁, v₂] with hvs
  set lam : Fin 3 → F := ![ω, 1, ω ^ 2] with hlam
  have hev : ∀ j, M *ᵥ vs j = lam j • vs j := by
    intro j
    fin_cases j
    · exact hv₀
    · exact hv₁
    · exact hv₂
  have hne : ∀ j, vs j ≠ 0 := by
    intro j
    fin_cases j
    · exact hv₀0
    · exact hv₁0
    · exact hv₂0
  set U : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j => vs j i with hU
  have hMU : M * U = U * diagonal lam := by
    ext i j
    have h1 : (M * U) i j = (M *ᵥ vs j) i := rfl
    rw [h1, hev j, Matrix.mul_diagonal]
    simp [hU, mul_comm]
  have hinj : Function.Injective lam := by
    have h01 : lam 0 ≠ lam 1 := hω1
    have h02 : lam 0 ≠ lam 2 := hωω
    have h12 : lam 1 ≠ lam 2 := fun h => hω2 h.symm
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd h h01
    · exact absurd h h02
    · exact absurd h h01.symm
    · rfl
    · exact absurd h h12
    · exact absurd h h02.symm
    · exact absurd h h12.symm
    · rfl
  have hli : LinearIndependent F U.col := by
    have := Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) lam hinj vs
      (fun j => by
        rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
        exact ⟨hev j, hne j⟩)
    exact this
  have hUunit : IsUnit U := Matrix.linearIndependent_cols_iff_isUnit.1 hli
  have hUdet : U.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det U).1 hUunit |>.ne_zero
  set G : Matrix (Fin 3) (Fin 3) F := conjTr σ U * S * U with hG
  have hDconj : conjTr σ (diagonal lam) = diagonal lam := by
    rw [conjTr_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [hlam, hσω, hσω2]
  have hGD : diagonal lam * G * diagonal lam = G := by
    calc diagonal lam * G * diagonal lam
        = conjTr σ (diagonal lam) * G * diagonal lam := by rw [hDconj]
      _ = conjTr σ (U * diagonal lam) * S * (U * diagonal lam) := by
          rw [conjTr_mul, hG]; simp only [Matrix.mul_assoc]
      _ = conjTr σ (M * U) * S * (M * U) := by rw [hMU]
      _ = conjTr σ U * (conjTr σ M * S * M) * U := by
          rw [conjTr_mul]; simp only [Matrix.mul_assoc]
      _ = G := by rw [hM]
  have hGs : conjTr σ G = G := by
    rw [hG, conjTr_mul, conjTr_mul, hS, conjTr_conjTr σ hσ]
    simp only [Matrix.mul_assoc]
  have hGe : ∀ i j, lam i * G i j * lam j = G i j := by
    intro i j
    have := congrFun (congrFun hGD i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    exact this
  have hG00 : G 0 0 = 0 := by
    have h := hGe 0 0
    simp only [hlam, Matrix.cons_val_zero] at h
    have : (ω ^ 2 - 1) * G 0 0 = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hω2)
  have hG01 : G 0 1 = 0 := by
    have h := hGe 0 1
    simp [hlam] at h
    have : (ω - 1) * G 0 1 = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hω1)
  have hG10 : G 1 0 = 0 := by
    have h := hGe 1 0
    simp [hlam] at h
    have : (ω - 1) * G 1 0 = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hω1)
  have hG12 : G 1 2 = 0 := by
    have h := hGe 1 2
    simp [hlam] at h
    have : (ω ^ 2 - 1) * G 1 2 = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hω2)
  have hG21 : G 2 1 = 0 := by
    have h := hGe 2 1
    simp [hlam] at h
    have : (ω ^ 2 - 1) * G 2 1 = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hω2)
  have hG22 : G 2 2 = 0 := by
    have h := hGe 2 2
    simp [hlam] at h
    have : (ω - 1) * G 2 2 = 0 := by
      have e : ω ^ 2 * ω ^ 2 = ω := by linear_combination ω * hω3
      linear_combination h - (G 2 2) * e
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hω1)
  have hdetG : G.det = σ U.det * S.det * U.det := by
    rw [hG, Matrix.det_mul, Matrix.det_mul, det_conjTr]
  have hdetG' : G.det = -(G 0 2 * G 1 1 * G 2 0) := by
    rw [Matrix.det_fin_three, hG00, hG01, hG10, hG12, hG21, hG22]
    ring
  have hGne : G 0 2 * G 1 1 * G 2 0 ≠ 0 := by
    intro h0
    have h1 : G.det = 0 := by rw [hdetG', h0, neg_zero]
    rw [hdetG] at h1
    exact mul_ne_zero (mul_ne_zero ((map_ne_zero σ).2 hUdet) hSdet) hUdet h1
  have ha : G 0 2 ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hGne)
  have hn : G 1 1 ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hGne)
  have hb : G 2 0 ≠ 0 := right_ne_zero_of_mul hGne
  have hσG : ∀ i j, σ (G j i) = G i j := fun i j => congrFun (congrFun hGs i) j
  have hbσ : G 2 0 = σ (G 0 2) := (hσG 2 0).symm
  have hnσ : σ (G 1 1) = G 1 1 := hσG 1 1
  obtain ⟨β, hβ⟩ := hnorm (G 1 1)⁻¹ (by rw [map_inv₀, hnσ]) (inv_ne_zero hn)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hβ
    exact inv_ne_zero hn hβ.symm
  set d : Fin 3 → F := ![1, β, (G 0 2)⁻¹] with hd
  set B : Matrix (Fin 3) (Fin 3) F := U * diagonal d with hB
  have e02 : σ (d 0) * G 0 2 * d 2 = 1 := by
    show σ 1 * G 0 2 * (G 0 2)⁻¹ = 1
    rw [map_one, one_mul, mul_inv_cancel₀ ha]
  have e11 : σ (d 1) * G 1 1 * d 1 = 1 := by
    show σ β * G 1 1 * β = 1
    calc σ β * G 1 1 * β = G 1 1 * (σ β * β) := by ring
      _ = G 1 1 * (G 1 1)⁻¹ := by rw [hβ]
      _ = 1 := mul_inv_cancel₀ hn
  have e20 : σ (d 2) * G 2 0 * d 0 = 1 := by
    show σ (G 0 2)⁻¹ * G 2 0 * 1 = 1
    rw [map_inv₀, ← hbσ, mul_one, inv_mul_cancel₀ hb]
  refine ⟨B, ?_, ?_, ?_⟩
  · rw [hB, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three]
    exact mul_ne_zero hUdet (mul_ne_zero (mul_ne_zero one_ne_zero hβ0) (inv_ne_zero ha))
  · have hBG : conjTr σ B * S * B = diagonal (fun i => σ (d i)) * G * diagonal d := by
      rw [hB, conjTr_mul, conjTr_diagonal, hG]
      simp only [Matrix.mul_assoc]
    rw [hBG]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    fin_cases i <;> fin_cases j
    · show σ (d 0) * G 0 0 * d 0 = antidiag 3 0 0
      rw [hG00]
      simp [antidiag]
    · show σ (d 0) * G 0 1 * d 1 = antidiag 3 0 1
      rw [hG01]
      simp [antidiag]
    · show σ (d 0) * G 0 2 * d 2 = antidiag 3 0 2
      rw [e02]
      simp [antidiag]
    · show σ (d 1) * G 1 0 * d 0 = antidiag 3 1 0
      rw [hG10]
      simp [antidiag]
    · show σ (d 1) * G 1 1 * d 1 = antidiag 3 1 1
      rw [e11]
      simp [antidiag]
    · show σ (d 1) * G 1 2 * d 2 = antidiag 3 1 2
      rw [hG12]
      simp [antidiag]
    · show σ (d 2) * G 2 0 * d 0 = antidiag 3 2 0
      rw [e20]
      simp [antidiag]
    · show σ (d 2) * G 2 1 * d 1 = antidiag 3 2 1
      rw [hG21]
      simp [antidiag]
    · show σ (d 2) * G 2 2 * d 2 = antidiag 3 2 2
      rw [hG22]
      simp [antidiag]
  · have hcomm : diagonal lam * diagonal d = diagonal d * diagonal lam := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    rw [hB, ← Matrix.mul_assoc, hMU, Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc]

end NormalForm

end CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
