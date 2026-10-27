module

public import CFSG.Quasithin.Vol2.Ch11SecS12R
public import CFSG.Quasithin.Vol2.Ch11SecS12YA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
theorem cube_eq_one_of_card_four (hF : Nat.card F = 4) {x : F} (hx : x ≠ 0) : x ^ 3 = 1 := by
  have := Fintype.ofFinite F
  have h := FiniteField.pow_card_sub_one_eq_one x hx
  rwa [← Nat.card_eq_fintype_card, hF] at h

theorem exists_diag_conj (hF : Nat.card F = 4) {j : Fin 2} {g : GL (Fin 3) F}
    (hgN : ProjGenLinGroup.mk g ∈
      Subgroup.normalizer ((pCoreOf 2 (Ptheta F j) : Subgroup (PGL3 F)) : Set (PGL3 F)))
    (hgsc : ProjGenLinGroup.mk g ∈ sectionCentralizer (Ptheta F j) (pCoreOf 2 (Ptheta F j)))
    (hg3 : ProjGenLinGroup.mk g ^ 3 = 1) (hg1 : ProjGenLinGroup.mk g ≠ 1) :
    ∃ m : GL (Fin 3) F, ∃ a d : F, a ≠ d ∧
      ((m * g * m⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal ![a, d, d] := by
  have hne : ProjGenLinGroup.mk g ^ 2 ≠ 1 := fun h2 => hg1 (eq_one_of_sq_of_cube h2 hg3)
  fin_cases j
  · obtain ⟨h10, h20⟩ := entries_of_normalizer_zero hF hgN
    obtain ⟨h12, h21, h11⟩ := block_of_mem_sc_zero hF hgsc h10 h20
    have had : (g : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ (g : Matrix (Fin 3) (Fin 3) F) 1 1 :=
      fun h => hne (sq_mk_eq_one_zero h10 h20 h12 h21 h11 h)
    obtain ⟨m, hm⟩ := exists_conj_diag_zero h10 h20 h12 h21 h11 had
    exact ⟨m, _, _, had, hm⟩
  · obtain ⟨h20, h21⟩ := entries_of_normalizer_one hF hgN
    obtain ⟨h01, h10, h00⟩ := block_of_mem_sc_one hF hgsc h20 h21
    have had : (g : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ (g : Matrix (Fin 3) (Fin 3) F) 0 0 :=
      fun h => hne (sq_mk_eq_one_one h20 h21 h01 h10 h00 h)
    obtain ⟨m, hm⟩ := exists_conj_diag_one h20 h21 h01 h10 h00 had
    exact ⟨m, _, _, had, hm⟩

omit [CharP F 2] in
theorem lower_cube_eq_one (hF : Nat.card F = 4) {h : GL (Fin 3) F}
    (h01 : (h : Matrix (Fin 3) (Fin 3) F) 0 1 = 0) (h02 : (h : Matrix (Fin 3) (Fin 3) F) 0 2 = 0)
    (h10 : (h : Matrix (Fin 3) (Fin 3) F) 1 0 = 0) (h20 : (h : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h3 : ProjGenLinGroup.mk h ^ 3 = 1) :
    (h : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 ∧
    !![(h : Matrix (Fin 3) (Fin 3) F) 1 1, (h : Matrix (Fin 3) (Fin 3) F) 1 2;
        (h : Matrix (Fin 3) (Fin 3) F) 2 1, (h : Matrix (Fin 3) (Fin 3) F) 2 2] *
      !![(h : Matrix (Fin 3) (Fin 3) F) 1 1, (h : Matrix (Fin 3) (Fin 3) F) 1 2;
        (h : Matrix (Fin 3) (Fin 3) F) 2 1, (h : Matrix (Fin 3) (Fin 3) F) 2 2] *
      !![(h : Matrix (Fin 3) (Fin 3) F) 1 1, (h : Matrix (Fin 3) (Fin 3) F) 1 2;
        (h : Matrix (Fin 3) (Fin 3) F) 2 1, (h : Matrix (Fin 3) (Fin 3) F) 2 2] = 1 := by
  have hdet : (h : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have h00 : (h : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := by
    intro h0
    apply hdet
    rw [Matrix.det_fin_three, h0, h01, h02]
    ring
  refine ⟨h00, ?_⟩
  rw [← map_pow, ProjGenLinGroup.mk_eq_one,
    GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at h3
  obtain ⟨μ, hμ⟩ := h3
  have hμ' : ∀ i j, ((h : Matrix (Fin 3) (Fin 3) F) * h * h) i j = scalar (Fin 3) μ i j := by
    intro i j
    rw [hμ, show h ^ 3 = h * h * h by rw [pow_three, mul_assoc], Units.val_mul, Units.val_mul]
  have e00 := hμ' 0 0
  have e11 := hμ' 1 1
  have e12 := hμ' 1 2
  have e21 := hμ' 2 1
  have e22 := hμ' 2 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply, Matrix.diagonal_apply,
    h01, h02, h10, h20] at e00 e11 e12 e21 e22
  simp at e00 e11 e12 e21 e22
  have hμ1 : μ = 1 := by
    rw [← cube_eq_one_of_card_four hF h00, ← e00]
    ring
  rw [hμ1] at e11 e22
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;> simp
  · linear_combination e11
  · linear_combination e12
  · linear_combination e21
  · linear_combination e22

omit [Finite F] [CharP F 2] in
theorem exists_block_conj {h : GL (Fin 3) F}
    (h01 : (h : Matrix (Fin 3) (Fin 3) F) 0 1 = 0) (h02 : (h : Matrix (Fin 3) (Fin 3) F) 0 2 = 0)
    (h10 : (h : Matrix (Fin 3) (Fin 3) F) 1 0 = 0) (h20 : (h : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    {P : Matrix (Fin 2) (Fin 2) F} (hP : P.det ≠ 0) {β₁ β₂ : F}
    (hBP : !![(h : Matrix (Fin 3) (Fin 3) F) 1 1, (h : Matrix (Fin 3) (Fin 3) F) 1 2;
        (h : Matrix (Fin 3) (Fin 3) F) 2 1, (h : Matrix (Fin 3) (Fin 3) F) 2 2] * P =
      P * diagonal ![β₁, β₂]) :
    ∃ C : GL (Fin 3) F, (∀ a d : F, (C : Matrix (Fin 3) (Fin 3) F) * diagonal ![a, d, d] =
        diagonal ![a, d, d] * C) ∧
      ((C⁻¹ * h * C : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        diagonal ![(h : Matrix (Fin 3) (Fin 3) F) 0 0, β₁, β₂] := by
  set Cm : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, P 0 0, P 0 1; 0, P 1 0, P 1 1] with hCm
  have hdet : Cm.det ≠ 0 := by
    rw [hCm, Matrix.det_fin_three]
    rw [Matrix.det_fin_two] at hP
    simpa using hP
  have hval : ((GeneralLinearGroup.mkOfDetNeZero Cm hdet : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = Cm := rfl
  refine ⟨GeneralLinearGroup.mkOfDetNeZero Cm hdet, fun a d => ?_, ?_⟩
  · rw [hval, hCm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;> simp <;>
      ring
  · have hb : ∀ i j, (!![(h : Matrix (Fin 3) (Fin 3) F) 1 1, (h : Matrix (Fin 3) (Fin 3) F) 1 2;
        (h : Matrix (Fin 3) (Fin 3) F) 2 1, (h : Matrix (Fin 3) (Fin 3) F) 2 2] * P) i j =
        (P * diagonal ![β₁, β₂]) i j := fun i j => by rw [hBP]
    have b00 := hb 0 0
    have b01 := hb 0 1
    have b10 := hb 1 0
    have b11 := hb 1 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at b00 b01 b10 b11
    simp at b00 b01 b10 b11
    have hhC : (h : Matrix (Fin 3) (Fin 3) F) * Cm =
        Cm * diagonal ![(h : Matrix (Fin 3) (Fin 3) F) 0 0, β₁, β₂] := by
      rw [hCm]
      ext i j
      fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
        simp [h01, h02, h10, h20]
      all_goals first
        | linear_combination b00
        | linear_combination b01
        | linear_combination b10
        | linear_combination b11
    rw [Units.val_mul, Units.val_mul, hval, Matrix.mul_assoc, hhC, ← Matrix.mul_assoc]
    have hinv : (((GeneralLinearGroup.mkOfDetNeZero Cm hdet)⁻¹ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) * Cm = 1 := by
      have h1 := Units.inv_mul (GeneralLinearGroup.mkOfDetNeZero Cm hdet)
      rwa [hval] at h1
    rw [hinv, Matrix.one_mul]

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
