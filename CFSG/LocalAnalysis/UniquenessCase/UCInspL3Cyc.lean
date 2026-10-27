module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

open Matrix

section Char

variable {F : Type} [Field F]

@[expose] def sInv (M : Matrix (Fin 3) (Fin 3) F) : F :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0 + (M 0 0 * M 2 2 - M 0 2 * M 2 0) +
    (M 1 1 * M 2 2 - M 1 2 * M 2 1)

theorem ch3 (M : Matrix (Fin 3) (Fin 3) F) :
    M * M * M - M.trace • (M * M) + sInv M • M - M.det • (1 : Matrix (Fin 3) (Fin 3) F) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.trace_fin_three, Matrix.det_fin_three,
      sInv, Matrix.one_apply] <;> ring

theorem det_sub_one (M : Matrix (Fin 3) (Fin 3) F) :
    (M - 1).det = M.det - 1 + M.trace - sInv M := by
  simp [Matrix.det_fin_three, Matrix.trace_fin_three, sInv, Matrix.one_apply]
  ring

theorem charpoly_cube_of_not_scalar (M : Matrix (Fin 3) (Fin 3) F) (hM3 : M * M * M = 1)
    (hdet : M.det = 1) (hns : ∀ c : F, M ≠ c • (1 : Matrix (Fin 3) (Fin 3) F)) :
    M.trace = 0 ∧ sInv M = 0 := by
  have hch := ch3 M
  rw [hM3, hdet, one_smul] at hch
  have h1 : M.trace • (M * M) = sInv M • M := by
    calc M.trace • (M * M) = sInv M • M - (1 - M.trace • (M * M) + sInv M • M - 1) := by abel
      _ = sInv M • M := by rw [hch, sub_zero]
  have h2 : sInv M • (1 : Matrix (Fin 3) (Fin 3) F) = M.trace • M := by
    have h := congrArg (fun X => (M * M) * X) h1.symm
    simp only [Matrix.mul_smul] at h
    have e2 : M * M * (M * M) = M := by rw [← Matrix.mul_assoc, hM3, Matrix.one_mul]
    rw [hM3, e2] at h
    exact h
  have ht : M.trace = 0 := by
    by_contra ht
    apply hns (M.trace⁻¹ * sInv M)
    calc M = M.trace⁻¹ • (M.trace • M) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      _ = (M.trace⁻¹ * sInv M) • (1 : Matrix (Fin 3) (Fin 3) F) := by
          rw [← h2, smul_smul]
  refine ⟨ht, ?_⟩
  rw [ht, zero_smul] at h2
  have := congrFun (congrFun h2 0) 0
  simpa using this

theorem exists_fixed_of_cube (M : Matrix (Fin 3) (Fin 3) F) (hM3 : M * M * M = 1)
    (hdet : M.det = 1) (hns : ∀ c : F, M ≠ c • (1 : Matrix (Fin 3) (Fin 3) F)) :
    ∃ v : Fin 3 → F, v ≠ 0 ∧ M *ᵥ v = v := by
  obtain ⟨ht, hs⟩ := charpoly_cube_of_not_scalar M hM3 hdet hns
  have hd : (M - 1).det = 0 := by rw [det_sub_one, hdet, ht, hs]; ring
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  refine ⟨v, hv0, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
  exact hv

@[expose] def cycMat : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem exists_cyclic3 (h3 : (3 : F) ≠ 0) (hω : ∀ c : F, c ^ 2 + c + 1 ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) F) (hM3 : M * M * M = 1) (hM1 : M ≠ 1) (hdet : M.det = 1)
    (hns : ∀ c : F, M ≠ c • (1 : Matrix (Fin 3) (Fin 3) F)) :
    ∃ P : Matrix (Fin 3) (Fin 3) F, P.det ≠ 0 ∧ M * P = P * cycMat := by
  obtain ⟨v₁, hv₁0, hv₁⟩ := exists_fixed_of_cube M hM3 hdet hns
  have hw : ∃ w : Fin 3 → F, (M - 1) *ᵥ w ≠ 0 := by
    by_contra h
    push Not at h
    apply hM1
    have h0 : M - 1 = 0 := by
      ext i j
      have := congrFun (h (Pi.single j 1)) i
      simpa [Matrix.mulVec_single_one] using this
    exact sub_eq_zero.1 h0
  obtain ⟨w, hw0⟩ := hw
  set v₂ : Fin 3 → F := (M - 1) *ᵥ w with hv₂def
  set x : Fin 3 → F := M *ᵥ v₂ with hxdef
  have hMx : M *ᵥ x = -x - v₂ := by
    have e : (M * M + M + 1) * (M - 1) = M * M * M - 1 := by noncomm_ring
    have h0 : ((M * M + M + 1) * (M - 1)) *ᵥ w = 0 := by
      rw [e, hM3, sub_self, Matrix.zero_mulVec]
    rw [← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec] at h0
    have h1 : M *ᵥ (M *ᵥ v₂) + M *ᵥ v₂ + v₂ = 0 := h0
    have h2 : M *ᵥ x + x + v₂ = 0 := h1
    rw [eq_sub_iff_add_eq, ← sub_eq_zero]
    rw [← h2]
    abel
  have hMv₂ : M *ᵥ v₂ = x := rfl
  set u : Fin 3 → F := v₁ + v₂ with hudef
  have hMu : M *ᵥ u = v₁ + x := by rw [hudef, Matrix.mulVec_add, hv₁]
  have hMMu : M *ᵥ (M *ᵥ u) = v₁ + (-x - v₂) := by rw [hMu, Matrix.mulVec_add, hv₁, hMx]
  have hM3u : M *ᵥ (M *ᵥ (M *ᵥ u)) = u := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM3, Matrix.one_mulVec]
  set P : Matrix (Fin 3) (Fin 3) F :=
    Matrix.of fun i j => (![u, M *ᵥ u, M *ᵥ (M *ᵥ u)] : Fin 3 → Fin 3 → F) j i with hPdef
  have hPc : ∀ c : Fin 3 → F,
      P *ᵥ c = c 0 • u + c 1 • (M *ᵥ u) + c 2 • (M *ᵥ (M *ᵥ u)) := by
    intro c
    ext i
    simp [hPdef, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  refine ⟨P, ?_, ?_⟩
  · intro hd
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    rw [hPc, hMMu, hMu] at hc
    apply hc0
    set a : F := c 0 + c 1 + c 2 with ha
    set b : F := c 0 - c 2 with hb
    set c' : F := c 1 - c 2 with hc'
    have E1 : a • v₁ + b • v₂ + c' • x = 0 := by
      rw [← hc, hudef, ha, hb, hc']
      module
    have E2 : a • v₁ + b • x + c' • (-x - v₂) = 0 := by
      have := congrArg (fun y => M *ᵥ y) E1
      simpa only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_zero, hv₁, hMv₂, hMx]
        using this
    have E3 : a • v₁ + (b - c') • (-x - v₂) - c' • x = 0 := by
      have := congrArg (fun y => M *ᵥ y) E2
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_zero, Matrix.mulVec_sub,
        Matrix.mulVec_neg, hv₁, hMv₂, hMx] at this
      rw [← this]
      module
    have h3a : (3 * a) • v₁ = 0 := by
      calc (3 * a) • v₁ = (a • v₁ + b • v₂ + c' • x) + (a • v₁ + b • x + c' • (-x - v₂)) +
          (a • v₁ + (b - c') • (-x - v₂) - c' • x) := by module
        _ = 0 := by rw [E1, E2, E3]; simp
    have ha0 : a = 0 := by
      rcases smul_eq_zero.1 h3a with h | h
      · exact (mul_eq_zero.1 h).resolve_left h3
      · exact absurd h hv₁0
    have E1' : b • v₂ + c' • x = 0 := by
      rw [ha0, zero_smul, zero_add] at E1
      exact E1
    have hc'0 : c' = 0 := by
      by_contra hne
      have hxl : x = (-b / c') • v₂ := by
        have : c' • x = (-b) • v₂ := by
          have h' : c' • x = -(b • v₂) := eq_neg_of_add_eq_zero_right E1'
          rw [h', neg_smul]
        calc x = c'⁻¹ • (c' • x) := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
          _ = c'⁻¹ • ((-b) • v₂) := by rw [this]
          _ = (-b / c') • v₂ := by rw [smul_smul, div_eq_inv_mul]
      set l : F := -b / c' with hl
      have hMx2 : M *ᵥ x = l • x := by rw [hxl, Matrix.mulVec_smul, hMv₂, ← hxl]
      have hrel : (l ^ 2 + l + 1) • v₂ = 0 := by
        have h1 : M *ᵥ x = l • (l • v₂) := by rw [hMx2, ← hxl, hxl]
        have h2 : -x - v₂ = l • (l • v₂) := by rw [← hMx, h1]
        calc (l ^ 2 + l + 1) • v₂ = l • (l • v₂) + l • v₂ + v₂ := by module
          _ = 0 := by rw [← h2, ← hxl]; abel
      rcases smul_eq_zero.1 hrel with h | h
      · exact hω l h
      · exact hw0 h
    have hb0 : b = 0 := by
      rw [hc'0, zero_smul, add_zero] at E1'
      rcases smul_eq_zero.1 E1' with h | h
      · exact h
      · exact absurd h hw0
    have h2c : c 0 = c 2 := by linear_combination hb0
    have h2c' : c 1 = c 2 := by linear_combination hc'0
    have h3c : 3 * c 2 = 0 := by linear_combination ha0 + (-1 : F) * h2c + (-1 : F) * h2c'
    have hc2 : c 2 = 0 := (mul_eq_zero.1 h3c).resolve_left h3
    ext i
    fin_cases i
    · simp [h2c, hc2]
    · simp [h2c', hc2]
    · simp [hc2]
  · have hcol0 : (fun k => P k 0) = u := by ext k; simp [hPdef]
    have hcol1 : (fun k => P k 1) = M *ᵥ u := by ext k; simp [hPdef]
    have hcol2 : (fun k => P k 2) = M *ᵥ (M *ᵥ u) := by ext k; simp [hPdef]
    ext i j
    have hMP : ∀ j, (M * P) i j = (M *ᵥ fun k => P k j) i := fun j => rfl
    fin_cases j
    · show (M * P) i 0 = (P * (cycMat : Matrix (Fin 3) (Fin 3) F)) i 0
      rw [hMP, hcol0]
      simp [cycMat, Matrix.mul_apply, Fin.sum_univ_three, hPdef]
    · show (M * P) i 1 = (P * (cycMat : Matrix (Fin 3) (Fin 3) F)) i 1
      rw [hMP, hcol1]
      simp [cycMat, Matrix.mul_apply, Fin.sum_univ_three, hPdef]
    · show (M * P) i 2 = (P * (cycMat : Matrix (Fin 3) (Fin 3) F)) i 2
      rw [hMP, hcol2, hM3u]
      simp [cycMat, Matrix.mul_apply, Fin.sum_univ_three, hPdef]

theorem exists_conj3 (h3 : (3 : F) ≠ 0) (hω : ∀ c : F, c ^ 2 + c + 1 ≠ 0)
    (M N : Matrix (Fin 3) (Fin 3) F) (hM3 : M * M * M = 1) (hMdet : M.det = 1)
    (hMns : ∀ c : F, M ≠ c • (1 : Matrix (Fin 3) (Fin 3) F))
    (hN3 : N * N * N = 1) (hNdet : N.det = 1)
    (hNns : ∀ c : F, N ≠ c • (1 : Matrix (Fin 3) (Fin 3) F)) :
    ∃ Q : GL (Fin 3) F,
      (Q : Matrix (Fin 3) (Fin 3) F) * M = N * (Q : Matrix (Fin 3) (Fin 3) F) := by
  obtain ⟨PM, hPM, hMP⟩ := exists_cyclic3 h3 hω M hM3 (by simpa using hMns 1) hMdet hMns
  obtain ⟨PN, hPN, hNP⟩ := exists_cyclic3 h3 hω N hN3 (by simpa using hNns 1) hNdet hNns
  let GM : GL (Fin 3) F := Matrix.GeneralLinearGroup.mkOfDetNeZero PM hPM
  let GN : GL (Fin 3) F := Matrix.GeneralLinearGroup.mkOfDetNeZero PN hPN
  have hGM : (GM : Matrix (Fin 3) (Fin 3) F) = PM := rfl
  have hGN : (GN : Matrix (Fin 3) (Fin 3) F) = PN := rfl
  refine ⟨GN * GM⁻¹, ?_⟩
  set Pi : Matrix (Fin 3) (Fin 3) F := ((GM⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hPi
  have hPiPM : Pi * PM = 1 := by rw [← hGM]; exact Units.inv_mul GM
  have hPMPi : PM * Pi = 1 := by rw [← hGM]; exact Units.mul_inv GM
  have h1 : Pi * M = cycMat * Pi := by
    calc Pi * M = Pi * M * (PM * Pi) := by rw [hPMPi, Matrix.mul_one]
      _ = Pi * (M * PM) * Pi := by simp only [Matrix.mul_assoc]
      _ = Pi * (PM * cycMat) * Pi := by rw [hMP]
      _ = (Pi * PM) * cycMat * Pi := by simp only [Matrix.mul_assoc]
      _ = cycMat * Pi := by rw [hPiPM, Matrix.one_mul]
  rw [Units.val_mul, hGN]
  calc PN * Pi * M = PN * (Pi * M) := Matrix.mul_assoc _ _ _
    _ = PN * (cycMat * Pi) := by rw [h1]
    _ = (PN * cycMat) * Pi := (Matrix.mul_assoc _ _ _).symm
    _ = (N * PN) * Pi := by rw [← hNP]
    _ = N * (PN * Pi) := Matrix.mul_assoc _ _ _

end Char

end CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
