module

public import CFSG.RankThree.PartOne.KF.UnitaryDiag
import CFSG.RankThree.PartOne.KF.UnitaryTorus

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZQ3

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {f : ℕ} {K' : Type} [Field K']

section Aux

open Matrix CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

private theorem exists_diag_mul_mem (h : UnitaryFieldData 2 f K')
    (P : primeFormUnitary h (idGram K' 3)) :
    ∃ u : K'ˣ, (P : GL (Fin 3) K') * diagU ![u, 1, 1] ∈ unitarySU 2 f K' 3 := by
  classical
  have hPu : (((P : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K').map h.bar)ᵀ *
      ((P : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') = 1 := by
    have h1 := (mem_primeFormUnitary (h := h)).1 P.2
    simpa only [idGram, Units.val_one, Matrix.mul_one] using h1
  have hd0 : ((P : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K').det ≠ 0 :=
    (Matrix.isUnits_det_units (P : GL (Fin 3) K')).ne_zero
  have hdN : h.bar ((P : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K').det *
      ((P : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K').det = 1 := by
    have h1 := congrArg Matrix.det hPu
    have h2 : ((((P : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K').map h.bar)ᵀ).det =
        h.bar ((P : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K').det := by
      rw [Matrix.det_transpose]
      exact (RingHom.map_det (h.bar : K' →+* K') _).symm
    rwa [Matrix.det_mul, h2, Matrix.det_one] at h1
  set u : K'ˣ := (Units.mk0 _ hd0)⁻¹ with hu_def
  have hu : h.bar (u : K') * (u : K') = 1 := by
    simp only [hu_def, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀]
    rw [← mul_inv, hdN, inv_one]
  have hD : (diagU ![u, 1, 1] : GL (Fin 3) K') ∈ primeFormUnitary h (idGram K' 3) := by
    rw [mem_primeFormUnitary]
    simp only [idGram, Units.val_one, Matrix.mul_one, diagU_val]
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i
    · simpa using hu
    · simp
    · simp
  refine ⟨u, ?_⟩
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Matrix.det_mul, det_diagU, Fin.prod_univ_three]
    simp [hu_def, hd0]
  · have h1 := (mem_primeFormUnitary (h := h)).1 (mul_mem P.2 hD)
    simpa only [idGram, Units.val_one, Matrix.mul_one] using h1

end Aux

theorem exists_conj_diag_of_three (h : UnitaryFieldData 2 f K') (hpq : 3 ∣ 2 ^ f + 1)
    (F : Subgroup (unitarySU 2 f K' 3)) (hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x)
    (hexp : ∀ x ∈ F, x ^ 3 = 1) :
    ∃ P : unitarySU 2 f K' 3, ∀ x ∈ F, ∀ i j : Fin 3, i ≠ j →
      (((P⁻¹ * x * P : unitarySU 2 f K' 3) : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') i j = 0 := by
  open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KCUnitaryModel
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher in
  classical
  have hle : unitarySU 2 f K' 3 ≤ primeFormUnitary h (idGram K' 3) :=
    unitarySU_le_primeFormUnitary h
  let G : Subgroup (primeFormUnitary h (idGram K' 3)) := F.map (Subgroup.inclusion hle)
  have hcommG : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  have hpowG : ∀ x ∈ G, x ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hexp a ha, map_one]
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag h Nat.prime_three hpq G hcommG hpowG
  obtain ⟨u, hu⟩ := exists_diag_mul_mem h P
  refine ⟨⟨(P : GL (Fin 3) K') * diagU ![u, 1, 1], hu⟩, fun x hx i j hij => ?_⟩
  have hdiag := hP (Subgroup.inclusion hle x) ⟨x, hx, rfl⟩
  have key : ∀ Δ : GL (Fin 3) K', (Δ : Matrix (Fin 3) (Fin 3) K') i j = 0 →
      (((diagU ![u, 1, 1])⁻¹ * Δ * diagU ![u, 1, 1] : GL (Fin 3) K') :
        Matrix (Fin 3) (Fin 3) K') i j = 0 := by
    intro Δ hΔ
    have hinv : (diagU ![u, 1, 1] : GL (Fin 3) K')⁻¹ = diagU (![u, 1, 1])⁻¹ :=
      (map_inv (diagUHom : (Fin 3 → K'ˣ) →* GL (Fin 3) K') _).symm
    rw [Units.val_mul, Units.val_mul, hinv, diagU_val, diagU_val, Matrix.mul_diagonal,
      Matrix.diagonal_mul, hΔ]
    simp
  have e : ((⟨(P : GL (Fin 3) K') * diagU ![u, 1, 1], hu⟩⁻¹ * x *
      ⟨(P : GL (Fin 3) K') * diagU ![u, 1, 1], hu⟩ : unitarySU 2 f K' 3) : GL (Fin 3) K') =
      (diagU ![u, 1, 1])⁻¹ * ((P : GL (Fin 3) K')⁻¹ * (x : GL (Fin 3) K') * (P : GL (Fin 3) K')) *
        diagU ![u, 1, 1] := by
    change ((P : GL (Fin 3) K') * diagU ![u, 1, 1])⁻¹ * (x : GL (Fin 3) K') *
      ((P : GL (Fin 3) K') * diagU ![u, 1, 1]) = _
    group
  rw [e]
  exact key _ (hdiag hij)

end CFSG.RankThree.PartOne.SEITZQ3
