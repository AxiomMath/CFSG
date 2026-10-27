module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag Matrix
open scoped MatrixGroups

variable {f : ℕ} {K : Type} [Field K] {F : Type} [Field F]

@[expose] def res1U3BlockMat (φ : F →+* K) (B : Matrix (Fin 2) (Fin 2) F) :
    Matrix (Fin 3) (Fin 3) K :=
  !![φ (B 0 0), 0, φ (B 0 1); 0, 1, 0; φ (B 1 0), 0, φ (B 1 1)]

theorem res1U3BlockMat_mul (φ : F →+* K) (A B : Matrix (Fin 2) (Fin 2) F) :
    res1U3BlockMat φ (A * B) = res1U3BlockMat φ A * res1U3BlockMat φ B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [res1U3BlockMat, Matrix.mul_apply, Fin.sum_univ_succ]

theorem res1U3BlockMat_one (φ : F →+* K) :
    res1U3BlockMat φ (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [res1U3BlockMat]

theorem res1U3BlockMat_det (φ : F →+* K) (B : Matrix (Fin 2) (Fin 2) F) :
    (res1U3BlockMat φ B).det = φ B.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [res1U3BlockMat]

theorem res1U3BlockMat_map_bar (h : UnitaryFieldData 2 f K) (φ : F →+* K)
    (hφ : ∀ x, h.bar (φ x) = φ x) (B : Matrix (Fin 2) (Fin 2) F) :
    (res1U3BlockMat φ B).map h.bar = res1U3BlockMat φ B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [res1U3BlockMat, hφ]

theorem res1U3BlockMat_preserves_gram [CharP K 2] (φ : F →+* K) (c : K)
    {B : Matrix (Fin 2) (Fin 2) F} (hB : B.det = 1) :
    (res1U3BlockMat φ B)ᵀ * !![0, 0, 1; 0, c, 0; 1, 0, 0] * res1U3BlockMat φ B =
      !![0, 0, 1; 0, c, 0; 1, 0, 0] := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdet : φ (B 0 0) * φ (B 1 1) - φ (B 0 1) * φ (B 1 0) = 1 := by
    have := congrArg φ hB
    rw [Matrix.det_fin_two] at this
    simpa using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [res1U3BlockMat, Matrix.mul_apply, Fin.sum_univ_succ]
  · linear_combination (φ (B 0 0) * φ (B 1 0)) * h2
  · linear_combination hdet + (φ (B 0 1) * φ (B 1 0)) * h2
  · linear_combination hdet + (φ (B 0 1) * φ (B 1 0)) * h2
  · linear_combination (φ (B 0 1) * φ (B 1 1)) * h2

theorem res1U3BlockMat_mul_diagonal (φ : F →+* K) (B : Matrix (Fin 2) (Fin 2) F)
    {δ : Fin 3 → K} (hδ : δ 0 = δ 2) :
    res1U3BlockMat φ B * diagonal δ = diagonal δ * res1U3BlockMat φ B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [res1U3BlockMat, Matrix.mul_diagonal, Matrix.diagonal_mul, hδ, mul_comm]

theorem res1U3BlockMat_injective (φ : F →+* K) : Function.Injective (res1U3BlockMat φ) := by
  intro A B h
  have h00 := congrFun (congrFun h 0) 0
  have h02 := congrFun (congrFun h 0) 2
  have h20 := congrFun (congrFun h 2) 0
  have h22 := congrFun (congrFun h 2) 2
  simp [res1U3BlockMat, φ.injective.eq_iff] at h00 h02 h20 h22
  ext i j
  fin_cases i <;> fin_cases j <;> simp [*]

private def res1U3Emb (φ : F →+* K) : SL(2, F) →* SL(3, K) where
  toFun B := ⟨res1U3BlockMat φ B, by rw [res1U3BlockMat_det, B.2, map_one]⟩
  map_one' := Subtype.ext (by simp [res1U3BlockMat_one])
  map_mul' A B := Subtype.ext (res1U3BlockMat_mul φ A B)

private theorem res1U3Emb_injective (φ : F →+* K) : Function.Injective (res1U3Emb φ) := by
  intro A B hAB
  have h : res1U3BlockMat φ (A : Matrix (Fin 2) (Fin 2) F) =
      res1U3BlockMat φ (B : Matrix (Fin 2) (Fin 2) F) := congrArg Subtype.val hAB
  exact Subtype.ext (res1U3BlockMat_injective φ h)

private theorem res1U3_unitary_conj (h : UnitaryFieldData 2 f K)
    {g gi E Γ : Matrix (Fin 3) (Fin 3) K} (hgi : g * gi = 1) (hgram : (g.map h.bar)ᵀ * g = Γ)
    (hE : E.map h.bar = E) (hEΓ : Eᵀ * Γ * E = Γ) :
    ((g * E * gi).map h.bar)ᵀ * (g * E * gi) = 1 := by
  calc ((g * E * gi).map h.bar)ᵀ * (g * E * gi)
      = (gi.map h.bar)ᵀ * (E.map h.bar)ᵀ * ((g.map h.bar)ᵀ * g) * E * gi := by
        rw [Matrix.map_mul, Matrix.map_mul, transpose_mul, transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = (gi.map h.bar)ᵀ * (Eᵀ * Γ * E) * gi := by
        rw [hgram, hE]
        simp only [Matrix.mul_assoc]
    _ = (gi.map h.bar)ᵀ * ((g.map h.bar)ᵀ * g) * gi := by rw [hEΓ, hgram]
    _ = ((g * gi).map h.bar)ᵀ * (g * gi) := by
        rw [Matrix.map_mul, transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hgi]
        simp

theorem res1U3_exists_slTwo_hom (h : UnitaryFieldData 2 f K) (φ : F →+* K)
    (hφ : ∀ x, h.bar (φ x) = φ x) {g : Matrix (Fin 3) (Fin 3) K} (hg : IsUnit g) {c : K}
    (hgram : (g.map h.bar)ᵀ * g = !![0, 0, 1; 0, c, 0; 1, 0, 0]) :
    ∃ ι : SL(2, F) →* unitarySU 2 f K 3, Function.Injective ι ∧
      ∀ (B : SL(2, F)) {W : Matrix (Fin 3) (Fin 3) K} {δ : Fin 3 → K}, δ 0 = δ 2 →
        W * g = g * diagonal δ →
          ((ι B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * W =
            W * ((ι B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  have : CharP K 2 := h.charP
  obtain ⟨u, rfl⟩ := hg
  let ι₀ : SL(2, F) →* GL (Fin 3) K :=
    (MulAut.conj u).toMonoidHom.comp (Matrix.SpecialLinearGroup.toGL.comp (res1U3Emb φ))
  have hι₀ : ∀ B : SL(2, F), ((ι₀ B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (u : Matrix (Fin 3) (Fin 3) K) * res1U3BlockMat φ B *
        ((u⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := fun B => rfl
  have hmem : ∀ B : SL(2, F), ι₀ B ∈ unitarySU 2 f K 3 := by
    intro B
    rw [mem_unitarySU_iff h, hι₀]
    refine ⟨?_, ?_⟩
    · rw [Matrix.det_units_conj u, res1U3BlockMat_det, B.2, map_one]
    · exact res1U3_unitary_conj h (Units.mul_inv u) hgram (res1U3BlockMat_map_bar h φ hφ B)
        (res1U3BlockMat_preserves_gram φ c B.2)
  have hinj : Function.Injective ι₀ := by
    intro A B hAB
    exact res1U3Emb_injective φ (Matrix.SpecialLinearGroup.toGL_injective
      ((MulAut.conj u).injective hAB))
  refine ⟨ι₀.codRestrict _ hmem, (MonoidHom.injective_codRestrict ι₀ _ hmem).mpr hinj, ?_⟩
  intro B W δ hδ hWg
  change ((ι₀ B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * W =
    W * ((ι₀ B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  rw [hι₀]
  set gm : Matrix (Fin 3) (Fin 3) K := (u : Matrix (Fin 3) (Fin 3) K)
  set gi : Matrix (Fin 3) (Fin 3) K := ((u⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hgig : gm * gi = 1 := Units.mul_inv u
  have higg : gi * gm = 1 := Units.inv_mul u
  have hgiW : gi * W = diagonal δ * gi :=
    calc gi * W = gi * W * (gm * gi) := by rw [hgig, Matrix.mul_one]
      _ = gi * (W * gm) * gi := by simp only [Matrix.mul_assoc]
      _ = gi * (gm * diagonal δ) * gi := by rw [hWg]
      _ = (gi * gm) * diagonal δ * gi := by simp only [Matrix.mul_assoc]
      _ = diagonal δ * gi := by rw [higg, Matrix.one_mul]
  have hcomm := res1U3BlockMat_mul_diagonal φ B hδ
  calc gm * res1U3BlockMat φ B * gi * W = gm * res1U3BlockMat φ B * (gi * W) := by
        simp only [Matrix.mul_assoc]
    _ = gm * res1U3BlockMat φ B * (diagonal δ * gi) := by rw [hgiW]
    _ = gm * (res1U3BlockMat φ B * diagonal δ) * gi := by simp only [Matrix.mul_assoc]
    _ = gm * (diagonal δ * res1U3BlockMat φ B) * gi := by rw [hcomm]
    _ = (gm * diagonal δ) * res1U3BlockMat φ B * gi := by simp only [Matrix.mul_assoc]
    _ = (W * gm) * res1U3BlockMat φ B * gi := by rw [hWg]
    _ = W * (gm * res1U3BlockMat φ B * gi) := by simp only [Matrix.mul_assoc]

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
