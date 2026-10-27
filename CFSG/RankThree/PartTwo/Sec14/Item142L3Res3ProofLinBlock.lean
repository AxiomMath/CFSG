module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofLinGL2
public import CFSG.LieType.SeitzGeneration.UnitaryHeisHom

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGLU27

open Matrix CFSG.LieType.SeitzGeneration

variable {K : Type} [Field K]

@[expose] def homL (ρ κ : K) (v φ : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  ρ • (1 : Matrix (Fin 3) (Fin 3) K) + κ • vecMulVec v φ

theorem conj_homL (P : GL (Fin 3) K) (ρ κ : K) (v φ : Fin 3 → K) :
    (P : Matrix (Fin 3) (Fin 3) K) * homL ρ κ v φ * ((P⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) =
      homL ρ κ ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
        (φ ᵥ* ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  have hPP : (P : Matrix (Fin 3) (Fin 3) K) * ((P⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [homL, homL, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, hPP, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul]

theorem diag_eq_homL₂ (x y : K) :
    diagonal ![y, y, x] = homL y (x - y) ![0, 0, 1] ![0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [homL]

section Frame

variable (w₀ w₁ w₂ r₀ r₁ r₂ : K)

@[expose] def linFrame : Matrix (Fin 3) (Fin 3) K :=
  !![0, w₀, r₁; 0, w₁, -r₀; 1, 0, 0]

theorem det_linFrame : (linFrame w₀ w₁ r₀ r₁).det = -(r₀ * w₀ + r₁ * w₁) := by
  rw [linFrame, Matrix.det_fin_three]
  simp
  ring

variable {w₀ w₁ w₂ r₀ r₁ r₂}

theorem linFrame_mul_diag (a : K) :
    linFrame w₀ w₁ r₀ r₁ * diagonal ![a⁻¹ ^ 2, a, a] =
      diagonal ![a, a, a⁻¹ ^ 2] * linFrame w₀ w₁ r₀ r₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [linFrame, Matrix.mul_apply, Matrix.diagonal_apply] <;> ring

theorem linFrame_mul_hom {a κ : K} (hrw : r₀ * w₀ + r₁ * w₁ + r₂ * w₂ = 1) :
    linFrame w₀ w₁ r₀ r₁ *
        !![a + κ * (w₂ * r₂), κ * (w₂ * (1 - r₂ * w₂)), 0;
          κ * r₂, a + κ * (1 - r₂ * w₂), 0; 0, 0, a] =
      homL a κ ![w₀, w₁, w₂] ![r₀, r₁, r₂] * linFrame w₀ w₁ r₀ r₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [linFrame, homL, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;>
    first | ring1 | linear_combination (-κ * w₀) * hrw | linear_combination (-κ * w₁) * hrw |
      linear_combination (κ * w₀) * hrw | linear_combination (κ * w₁) * hrw |
      linear_combination (-κ * w₂) * hrw

theorem linFrame_mul_diag' {a : K} (hδ : 1 - r₂ * w₂ ≠ 0)
    (hrw : r₀ * w₀ + r₁ * w₁ + r₂ * w₂ = 1) :
    linFrame w₀ w₁ r₀ r₁ * diagonal ![a⁻¹, a, 1] =
      !![1 + (a - 1) * (w₀ * (r₀ / (1 - r₂ * w₂))), (a - 1) * (w₀ * (r₁ / (1 - r₂ * w₂))), 0;
        (a - 1) * (w₁ * (r₀ / (1 - r₂ * w₂))), 1 + (a - 1) * (w₁ * (r₁ / (1 - r₂ * w₂))), 0;
        0, 0, a⁻¹] * linFrame w₀ w₁ r₀ r₁ := by
  have hrv : r₀ * w₀ + r₁ * w₁ = 1 - r₂ * w₂ := by linear_combination hrw
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [linFrame, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] <;>
    field_simp <;>
    first | ring1 | linear_combination (a - 1) * w₀ * hrv | linear_combination (a - 1) * w₁ * hrv |
      linear_combination (1 - a) * w₀ * hrv | linear_combination (1 - a) * w₁ * hrv

end Frame

theorem blockDetMat_diagonal₂ (x y : K) :
    blockDetMat (diagonal ![x, y]) = diagonal ![x, y, (x * y)⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockDetMat, Matrix.det_diagonal, Fin.prod_univ_two]

theorem sl2_block_mem_of_generic_lin [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p] (hKq : Nat.card K = p ^ f) (hq4 : 4 ≤ p ^ f) {a : K}
    (ha0 : a ≠ 0) (ha3 : 3 ≤ orderOf a) (h6 : 6 ≤ orderOf (a⁻¹ ^ 2 / a))
    (hsf : SubfieldOK p f (orderOf (a⁻¹ ^ 2 / a))) (H : Subgroup (GL (Fin 3) K))
    (hH0 : ∃ g ∈ H, (g : Matrix (Fin 3) (Fin 3) K) = diagonal ![a⁻¹ ^ 2, a, a])
    (hH2 : ∃ g ∈ H, (g : Matrix (Fin 3) (Fin 3) K) = diagonal ![a, a, a⁻¹ ^ 2])
    {z : GL (Fin 3) K} (hzH : z ∈ H) {w₀ w₁ w₂ r₀ r₁ r₂ : K}
    (hw : (z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1] = ![w₀, w₁, w₂])
    (hr : ![0, 0, 1] ᵥ* ((z⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = ![r₀, r₁, r₂])
    (hw0 : w₀ ≠ 0) (hw1 : w₁ ≠ 0) (hw2 : w₂ ≠ 0) (hr0 : r₀ ≠ 0) (hr1 : r₁ ≠ 0) (hr2 : r₂ ≠ 0)
    (hrw2 : r₂ * w₂ ≠ 1) :
    ∀ g : SpecialLinearGroup (Fin 2) K, blockOneGL (SpecialLinearGroup.toGL g) ∈ H := by
  classical
  have hrw : r₀ * w₀ + r₁ * w₁ + r₂ * w₂ = 1 := by
    have e : (![0, 0, 1] ᵥ* ((z⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ⬝ᵥ
        ((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) = 1 := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.vecMul_one]
      simp [dotProduct, Fin.sum_univ_three]
    rw [hw, hr] at e
    simpa [dotProduct, Fin.sum_univ_three] using e
  have hδ : 1 - r₂ * w₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm hrw2)
  set κ : K := a⁻¹ ^ 2 - a with hκ
  have hP0 : (linFrame w₀ w₁ r₀ r₁).det ≠ 0 := by
    rw [det_linFrame]
    intro h0
    apply hδ
    linear_combination (-1 : K) * hrw - h0
  set P₁ : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hP0 with hP₁
  have hP₁m : (P₁ : Matrix (Fin 3) (Fin 3) K) = linFrame w₀ w₁ r₀ r₁ := rfl
  have hconj : ∀ (M N : Matrix (Fin 3) (Fin 3) K) (g : GL (Fin 3) K),
      (g : Matrix (Fin 3) (Fin 3) K) = N → (P₁ : Matrix (Fin 3) (Fin 3) K) * M = N * P₁ →
      ∀ X : GL (Fin 2) K, (blockDetGL X : Matrix (Fin 3) (Fin 3) K) = M →
        P₁ * blockDetGL X * P₁⁻¹ = g := by
    intro M N g hg hMN X hX
    rw [mul_inv_eq_iff_eq_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hX, hMN, hg]
  obtain ⟨g₂, hg₂H, hg₂m⟩ := hH2
  obtain ⟨g₀, hg₀H, hg₀m⟩ := hH0
  have hgw : ((z * g₂ * z⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homL a κ ![w₀, w₁, w₂] ![r₀, r₁, r₂] := by
    rw [Units.val_mul, Units.val_mul, hg₂m, diag_eq_homL₂, conj_homL, hw, hr]
  have hgwH : z * g₂ * z⁻¹ ∈ H := H.mul_mem (H.mul_mem hzH hg₂H) (H.inv_mem hzH)
  have hA₁d : (diagonal ![a⁻¹ ^ 2, a] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    simp [Matrix.det_diagonal, Fin.prod_univ_two, ha0]
  set A₁ : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hA₁d with hA₁
  have hdetB₁ : (!![a + κ * (w₂ * r₂), κ * (w₂ * (1 - r₂ * w₂));
      κ * r₂, a + κ * (1 - r₂ * w₂)] : Matrix (Fin 2) (Fin 2) K).det = a⁻¹ := by
    rw [Matrix.det_fin_two_of, hκ]
    field_simp
    ring
  have hB₁d : (!![a + κ * (w₂ * r₂), κ * (w₂ * (1 - r₂ * w₂));
      κ * r₂, a + κ * (1 - r₂ * w₂)] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [hdetB₁]
    exact inv_ne_zero ha0
  set B₁ : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hB₁d with hB₁
  set Y₁ : Subgroup (GL (Fin 2) K) :=
    H.comap ((MulAut.conj P₁).toMonoidHom.comp blockDetGL) with hY₁
  have hA₁Y : A₁ ∈ Y₁ := by
    show P₁ * blockDetGL A₁ * P₁⁻¹ ∈ H
    rw [hconj (diagonal ![a⁻¹ ^ 2, a, a]) (diagonal ![a, a, a⁻¹ ^ 2]) g₂ hg₂m
      (by rw [hP₁m]; exact linFrame_mul_diag a) A₁
      (by
        rw [coe_blockDetGL]
        change blockDetMat (diagonal ![a⁻¹ ^ 2, a]) = _
        rw [blockDetMat_diagonal₂]
        congr 2
        field_simp)]
    exact hg₂H
  have hB₁Y : B₁ ∈ Y₁ := by
    show P₁ * blockDetGL B₁ * P₁⁻¹ ∈ H
    rw [hconj _ _ (z * g₂ * z⁻¹) hgw (by rw [hP₁m]; exact linFrame_mul_hom hrw) B₁
      (by
        rw [coe_blockDetGL]
        change blockDetMat !![a + κ * (w₂ * r₂), κ * (w₂ * (1 - r₂ * w₂));
          κ * r₂, a + κ * (1 - r₂ * w₂)] = _
        rw [blockDetMat_eq (by rw [hdetB₁, inv_inv])]
        ext i j
        fin_cases i <;> fin_cases j <;> rfl)]
    exact hgwH
  have hS1 := sl2_le_of_pair_lin hKq hq4 Y₁ (μ₁ := a⁻¹ ^ 2) (μ₂ := a) (ν₁ := a⁻¹ ^ 2) (ν₂ := a)
    (c := ![w₂, 1]) (ψ := ![r₂, 1 - r₂ * w₂]) (pow_ne_zero 2 (inv_ne_zero ha0)) ha0
    (pow_ne_zero 2 (inv_ne_zero ha0)) ha0 (by simp) hw2 one_ne_zero hr2 hδ h6 hsf
    (by omega) (A := A₁) (B := B₁) rfl
    (by
      change !![a + κ * (w₂ * r₂), κ * (w₂ * (1 - r₂ * w₂));
        κ * r₂, a + κ * (1 - r₂ * w₂)] = _
      rw [hκ]
      ext i j
      fin_cases i <;> fin_cases j <;> simp)
    hA₁Y hB₁Y
  have hD : (diagonal ![a⁻¹, a] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    simp [Matrix.det_diagonal, Fin.prod_univ_two, ha0]
  set D : SpecialLinearGroup (Fin 2) K := ⟨diagonal ![a⁻¹, a], hD⟩ with hDdef
  have hX₂d : (!![1 + (a - 1) * (w₀ * (r₀ / (1 - r₂ * w₂))), (a - 1) * (w₀ * (r₁ / (1 - r₂ * w₂)));
      (a - 1) * (w₁ * (r₀ / (1 - r₂ * w₂))), 1 + (a - 1) * (w₁ * (r₁ / (1 - r₂ * w₂)))] :
      Matrix (Fin 2) (Fin 2) K).det = a := by
    rw [Matrix.det_fin_two_of]
    field_simp
    linear_combination (a - 1) * (1 - r₂ * w₂) * hrw
  have hX₂d0 : (!![1 + (a - 1) * (w₀ * (r₀ / (1 - r₂ * w₂))),
      (a - 1) * (w₀ * (r₁ / (1 - r₂ * w₂)));
      (a - 1) * (w₁ * (r₀ / (1 - r₂ * w₂))), 1 + (a - 1) * (w₁ * (r₁ / (1 - r₂ * w₂)))] :
      Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [hX₂d]
    exact ha0
  set X₂ : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hX₂d0 with hX₂
  have hX₂H : blockDetGL X₂ ∈ H := by
    have hmem := hS1 D
    have e : P₁ * blockDetGL (SpecialLinearGroup.toGL D) * P₁⁻¹ = blockDetGL X₂ := by
      rw [mul_inv_eq_iff_eq_mul]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hP₁m, coe_blockDetGL, coe_blockDetGL]
      change linFrame w₀ w₁ r₀ r₁ * blockDetMat (diagonal ![a⁻¹, a]) =
        blockDetMat !![1 + (a - 1) * (w₀ * (r₀ / (1 - r₂ * w₂))),
          (a - 1) * (w₀ * (r₁ / (1 - r₂ * w₂)));
          (a - 1) * (w₁ * (r₀ / (1 - r₂ * w₂))), 1 + (a - 1) * (w₁ * (r₁ / (1 - r₂ * w₂)))] *
          linFrame w₀ w₁ r₀ r₁
      rw [blockDetMat_diagonal₂, blockDetMat_eq (by rw [hX₂d]),
        show (a⁻¹ * a)⁻¹ = (1 : K) by rw [inv_mul_cancel₀ ha0, inv_one]]
      exact linFrame_mul_diag' hδ hrw
    rw [← e]
    exact hmem
  set Y₂ : Subgroup (GL (Fin 2) K) := H.comap blockDetGL with hY₂
  have hA₁Y₂ : A₁ ∈ Y₂ := by
    show blockDetGL A₁ ∈ H
    have e : blockDetGL A₁ = g₀ := by
      apply Units.ext
      rw [coe_blockDetGL, hg₀m]
      change blockDetMat (diagonal ![a⁻¹ ^ 2, a]) = _
      rw [blockDetMat_diagonal₂]
      congr 2
      field_simp
    rw [e]
    exact hg₀H
  have hS2 := sl2_le_of_pair_lin hKq hq4 Y₂ (μ₁ := a⁻¹ ^ 2) (μ₂ := a) (ν₁ := a) (ν₂ := 1)
    (c := ![w₀, w₁]) (ψ := ![r₀ / (1 - r₂ * w₂), r₁ / (1 - r₂ * w₂)])
    (pow_ne_zero 2 (inv_ne_zero ha0)) ha0 ha0 one_ne_zero
    (by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp
      linear_combination hrw)
    hw0 hw1 (div_ne_zero hr0 hδ) (div_ne_zero hr1 hδ) h6 hsf (by rw [div_one]; exact ha3)
    (A := A₁) (B := X₂) rfl
    (by
      change !![1 + (a - 1) * (w₀ * (r₀ / (1 - r₂ * w₂))),
        (a - 1) * (w₀ * (r₁ / (1 - r₂ * w₂)));
        (a - 1) * (w₁ * (r₀ / (1 - r₂ * w₂))), 1 + (a - 1) * (w₁ * (r₁ / (1 - r₂ * w₂)))] = _
      ext i j
      fin_cases i <;> fin_cases j <;> simp)
    hA₁Y₂ hX₂H
  intro g
  have hdet : ((SpecialLinearGroup.toGL g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 :=
    g.2
  have hmem : blockDetGL (SpecialLinearGroup.toGL g) ∈ H := hS2 g
  rwa [show blockDetGL (SpecialLinearGroup.toGL g) = blockOneGL (SpecialLinearGroup.toGL g) from
    blockDetGL_eq_blockOneGL hdet] at hmem

theorem sl3_le_of_block (Q : Subgroup (GL (Fin 3) K))
    (hB : ∀ g : SpecialLinearGroup (Fin 2) K, blockOneGL (SpecialLinearGroup.toGL g) ∈ Q)
    {s : GL (Fin 3) K} (hs : (s : Matrix (Fin 3) (Fin 3) K) = !![0, 0, 1; 1, 0, 0; 0, 1, 0])
    (hsQ : s ∈ Q) : ∀ x : SpecialLinearGroup (Fin 3) K, SpecialLinearGroup.toGL x ∈ Q := by
  classical
  set K' : Subgroup (SpecialLinearGroup (Fin 3) K) := Q.comap SpecialLinearGroup.toGL with hK'
  have hshift : (shiftSL : SpecialLinearGroup (Fin 3) K) ∈ K' := by
    show SpecialLinearGroup.toGL shiftSL ∈ Q
    have e : SpecialLinearGroup.toGL (shiftSL : SpecialLinearGroup (Fin 3) K) = s := by
      apply Units.ext
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hs]
      rfl
    rw [e]
    exact hsQ
  have h01 : ∀ c : K, SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) c ∈ K' := by
    intro c
    show SpecialLinearGroup.toGL _ ∈ Q
    have e : SpecialLinearGroup.toGL (SpecialLinearGroup.transvection
        (by decide : (0 : Fin 3) ≠ 1) c) = blockOneGL (SpecialLinearGroup.toGL
          (SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) c)) := by
      apply Units.ext
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_blockOneGL,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [SpecialLinearGroup.transvection_coe, blockOneMat]
    rw [e]
    exact hB _
  have h10 : ∀ c : K, SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 0) c ∈ K' := by
    intro c
    show SpecialLinearGroup.toGL _ ∈ Q
    have e : SpecialLinearGroup.toGL (SpecialLinearGroup.transvection
        (by decide : (1 : Fin 3) ≠ 0) c) = blockOneGL (SpecialLinearGroup.toGL
          (SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) c)) := by
      apply Units.ext
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_blockOneGL,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [SpecialLinearGroup.transvection_coe, blockOneMat]
    rw [e]
    exact hB _
  have h12 := transvection_succ_mem hshift (by decide : (0 : Fin 3) ≠ 1) h01
  have h20 := transvection_succ_mem hshift (by decide : (0 : Fin 3) + 1 ≠ 1 + 1) h12
  have h21 := transvection_succ_mem hshift (by decide : (1 : Fin 3) ≠ 0) h10
  have h02 := transvection_succ_mem hshift (by decide : (1 : Fin 3) + 1 ≠ 0 + 1) h21
  have hall : ∀ (i j : Fin 3) (hij : i ≠ j) (c : K),
      SpecialLinearGroup.transvection hij c ∈ K' := by
    intro i j hij c
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | exact h01 c
      | exact h10 c
      | exact h12 c
      | exact h20 c
      | exact h21 c
      | exact h02 c
  have htop : (Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup
      (ι := Fin 3) (F := K)))) = ⊤ :=
    Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
  have hK'top : K' = ⊤ := by
    rw [eq_top_iff, ← htop, Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    exact hall t.i t.j t.hij t.c
  intro x
  have hx : x ∈ K' := hK'top ▸ Subgroup.mem_top x
  exact hx

end CFSG.RankThree.PartTwo.Sec14.L3PGLU27
