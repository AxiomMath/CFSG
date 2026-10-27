module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemL43

open Matrix

abbrev Mat4 : Type := Matrix (Fin 4) (Fin 4) (ZMod 3)

abbrev SL4 : Type := SpecialLinearGroup (Fin 4) (ZMod 3)

@[expose] def uMat (a b c d : ZMod 3) : Mat4 :=
  !![1, 1, a, b; 0, 1, c, d; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def vMat (a b c d : ZMod 3) : Mat4 :=
  !![1, 0, a, b; 0, 1, c, d; 0, 0, 1, 1; 0, 0, 0, 1]

@[expose] def rMat (a b c d : ZMod 3) : Mat4 :=
  !![1, 0, a, b; 0, 1, c, d; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def zMat : Mat4 := rMat 0 1 0 0

@[expose] def IsR (m : Mat4) : Prop := m = rMat (m 0 2) (m 0 3) (m 1 2) (m 1 3)

instance (m : Mat4) : Decidable (IsR m) := inferInstanceAs (Decidable (m = _))

@[expose] def p0Mat (i j k : ZMod 3) : Mat4 :=
  !![1, i, j, k; 0, 1, 0, i; 0, 0, 1, j; 0, 0, 0, 1]

@[expose] def IsP0 (m : Mat4) : Prop := m = p0Mat (m 0 1) (m 0 2) (m 0 3)

instance (m : Mat4) : Decidable (IsP0 m) := inferInstanceAs (Decidable (m = _))

@[expose] def phiMat (t : ZMod 3 × ZMod 3 × ZMod 3) : Mat4 :=
  p0Mat t.1 t.2.1 (t.2.2 + 2 * t.1 ^ 2 + t.1 + 2 * t.2.1 ^ 2 + t.2.1)

@[expose] def hOne (a : ZMod 3) : Mat4 :=
  !![1, 0, 0, 0; 0, -a, 1, 0; 0, 1, 0, 0; 0, 0, 0, -1]

@[expose] def hOneInv (a : ZMod 3) : Mat4 :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, a, 0; 0, 0, 0, -1]

@[expose] def hThree (a d : ZMod 3) : Mat4 :=
  !![1, 0, 0, 0; 0, 1, a, 0; 0, 0, d, 0; 0, 0, 0, d]

@[expose] def hThreeInv (a d : ZMod 3) : Mat4 :=
  !![1, 0, 0, 0; 0, 1, -a * d, 0; 0, 0, d, 0; 0, 0, 0, d]

@[expose] def nZero : Mat4 :=
  !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0; 0, 0, 0, 0]

@[expose] def cMat (α β γ δ ε μ : ZMod 3) : Mat4 :=
  !![α, β, γ, δ; 0, α, β, 0; 0, 0, α, 0; 0, 0, ε, μ]

@[expose] def o1Mat (α β γ δ : ZMod 3) : Mat4 :=
  !![α, β, γ, δ; 0, α, 0, β; 0, 0, α, γ; 0, 0, 0, α]

@[expose] def hBt : Fin 3 → Fin 3 → Mat4 :=
  ![![!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
      !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0],
      !![2, 2, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 2, 0]],
    ![!![2, 0, 0, 0; 0, 2, 0, 0; 0, 0, 0, 1; 0, 0, 2, 0],
      !![1, 0, 0, 0; 0, 2, 0, 2; 0, 2, 0, 1; 0, 0, 2, 0],
      !![1, 2, 0, 0; 0, 2, 0, 1; 0, 1, 0, 1; 0, 0, 2, 0]],
    ![!![1, 1, 0, 0; 0, 2, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
      !![2, 1, 0, 0; 0, 2, 0, 1; 0, 1, 0, 1; 0, 0, 1, 0],
      !![2, 2, 0, 0; 0, 2, 0, 2; 0, 2, 0, 1; 0, 0, 1, 0]]]

@[expose] def hBInvt : Fin 3 → Fin 3 → Mat4 :=
  ![![!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
      !![1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 0, 1, 0, 0],
      !![2, 0, 2, 0; 0, 0, 1, 0; 0, 0, 0, 2; 0, 1, 0, 0]],
    ![!![2, 0, 0, 0; 0, 2, 0, 0; 0, 0, 0, 2; 0, 0, 1, 0],
      !![1, 0, 0, 0; 0, 1, 1, 0; 0, 0, 0, 2; 0, 1, 2, 0],
      !![1, 1, 2, 0; 0, 1, 2, 0; 0, 0, 0, 2; 0, 2, 2, 0]],
    ![!![1, 1, 0, 0; 0, 2, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0],
      !![2, 1, 2, 0; 0, 1, 2, 0; 0, 0, 0, 1; 0, 2, 2, 0],
      !![2, 2, 2, 0; 0, 1, 1, 0; 0, 0, 0, 1; 0, 1, 2, 0]]]

@[expose] def hB (i j : ZMod 3) : Mat4 := hBt i j

@[expose] def hBInv (i j : ZMod 3) : Mat4 := hBInvt i j

@[expose] def uDual : Mat4 := !![1, 0, 0, 0; -1, 1, 0, 0; 0, 0, 1, 0; 1, -1, 0, 1]

@[expose] def vDual : Mat4 := !![1, 0, 0, 0; 0, 1, 0, 0; -1, 0, 1, 0; 1, 0, -1, 1]

@[expose] def zDual : Mat4 := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; -1, 0, 0, 1]

theorem three_eq_zero : (3 : ZMod 3) = 0 := by decide

theorem det_uMat (a b c d : ZMod 3) : (uMat a b c d).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [Fin.prod_univ_four, uMat]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [uMat]

theorem det_vMat (a b c d : ZMod 3) : (vMat a b c d).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [Fin.prod_univ_four, vMat]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [vMat]

theorem det_rMat (a b c d : ZMod 3) : (rMat a b c d).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [Fin.prod_univ_four, rMat]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [rMat]

theorem det_p0Mat (i j k : ZMod 3) : (p0Mat i j k).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [Fin.prod_univ_four, p0Mat]
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [p0Mat]

theorem p0Mat_mul (i j k i' j' k' : ZMod 3) :
    p0Mat i j k * p0Mat i' j' k' = p0Mat (i + i') (j + j') (k + k' + i * i' + j * j') := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem phiMat_add (s t : ZMod 3 × ZMod 3 × ZMod 3) :
    phiMat (s + t) = phiMat s * phiMat t := by
  obtain ⟨i, j, k⟩ := s
  obtain ⟨i', j', k'⟩ := t
  rw [phiMat, phiMat, phiMat, p0Mat_mul]
  simp only [Prod.mk_add_mk]
  congr 1
  linear_combination (i * i' + j * j') * three_eq_zero

theorem phiMat_zero : phiMat 0 = 1 := by decide

theorem isP0_phiMat (t : ZMod 3 × ZMod 3 × ZMod 3) : IsP0 (phiMat t) := by
  obtain ⟨i, j, k⟩ := t
  simp [IsP0, phiMat, p0Mat]

theorem exists_phiMat_of_isP0 {m : Mat4} (hm : IsP0 m) : ∃ t, phiMat t = m := by
  refine ⟨(m 0 1, m 0 2, m 0 3 - (2 * m 0 1 ^ 2 + m 0 1 + 2 * m 0 2 ^ 2 + m 0 2)), ?_⟩
  rw [hm, phiMat]
  simp only [p0Mat]
  congr 2
  simp
  ring

theorem phiMat_injective : Function.Injective phiMat := by
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
  have h1 := congrFun (congrFun h 0) 1
  have h2 := congrFun (congrFun h 0) 2
  have h3 := congrFun (congrFun h 0) 3
  simp [phiMat, p0Mat] at h1 h2 h3
  subst h1 h2
  simp only [Prod.mk.injEq, true_and]
  linear_combination h3

set_option maxRecDepth 10000 in
theorem hOne_facts : ∀ a : ZMod 3, (hOne a).det = 1 ∧ hOne a * hOneInv a = 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem hThree_facts : ∀ a d : ZMod 3, d ≠ 0 →
    (hThree a d).det = 1 ∧ hThree a d * hThreeInv a d = 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem k2a_check : ∀ a b : ZMod 3,
    IsR (hOneInv a * uMat a b 0 0 * hOne a) ∧ IsR (hOneInv a * zMat * hOne a) := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem k2b_check : ∀ a b' : ZMod 3, IsR (hOneInv a * vMat 0 b' 0 (-a) * hOne a) := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem k2c_check : ∀ a b d b' : ZMod 3,
    IsR (hOneInv (a - d) * (uMat a b 0 d * vMat (-d) b' 0 (-a)) * hOne (a - d)) := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem ns_check : ∀ a b b' d : ZMod 3, d ≠ 0 →
    IsP0 (hThree a d * uMat a b 0 d * hThreeInv a d) ∧
      IsP0 (hThree a d * vMat d b' 0 (-a) * hThreeInv a d) ∧
      IsP0 (hThree a d * zMat * hThreeInv a d) := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem hB_check : ∀ i j : ZMod 3, ¬ (i = 0 ∧ j = 0) →
    phiMat (i, j, 0) * hB i j = hB i j * (1 + nZero) ∧ hB i j * hBInv i j = 1 ∧
      (hB i j).det = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cMat_cube : ∀ α β γ δ ε μ : ZMod 3, (cMat α β γ δ ε μ).det = 1 →
    cMat α β γ δ ε μ ^ 3 = 1 ∨ cMat α β γ δ ε μ ^ 3 = -1 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem det_o1Mat : ∀ α β γ δ : ZMod 3, (o1Mat α β γ δ).det = α ^ 4 := by
  decide +kernel

theorem eq_of_uMat_mul_vMat_comm {a b c d a' b' c' d' : ZMod 3}
    (h : uMat a b c d * vMat a' b' c' d' = vMat a' b' c' d' * uMat a b c d) :
    c = 0 ∧ c' = 0 ∧ d' = -a := by
  have h02 := congrFun (congrFun h 0) 2
  have h03 := congrFun (congrFun h 0) 3
  have h13 := congrFun (congrFun h 1) 3
  simp [uMat, vMat, Matrix.mul_apply, Fin.sum_univ_four] at h02 h03 h13
  exact ⟨by linear_combination h13, by linear_combination h02, by linear_combination h03⟩

theorem eq_of_rMat_comm_uMat {x₀ x₁ x₂ x₃ a b d : ZMod 3}
    (h : rMat x₀ x₁ x₂ x₃ * uMat a b 0 d = uMat a b 0 d * rMat x₀ x₁ x₂ x₃) :
    x₂ = 0 ∧ x₃ = 0 := by
  have h02 := congrFun (congrFun h 0) 2
  have h03 := congrFun (congrFun h 0) 3
  simp [uMat, rMat, Matrix.mul_apply, Fin.sum_univ_four] at h02 h03
  exact ⟨by linear_combination -h02, by linear_combination -h03⟩

theorem eq_of_rMat_comm_vMat {x₀ x₁ x₂ x₃ a' b' d' : ZMod 3}
    (h : rMat x₀ x₁ x₂ x₃ * vMat a' b' 0 d' = vMat a' b' 0 d' * rMat x₀ x₁ x₂ x₃) :
    x₀ = 0 := by
  have h03 := congrFun (congrFun h 0) 3
  simp [vMat, rMat, Matrix.mul_apply, Fin.sum_univ_four] at h03
  linear_combination h03

theorem entry_comm_nZero {g : Mat4} (h : g * (1 + nZero) = (1 + nZero) * g) (i j : Fin 4) :
    (g * (1 + nZero)) i j = ((1 + nZero) * g) i j :=
  congrFun (congrFun h i) j

theorem eq_cMat_of_comm {g : Mat4} (h : g * (1 + nZero) = (1 + nZero) * g) :
    g = cMat (g 0 0) (g 0 1) (g 0 2) (g 0 3) (g 3 2) (g 3 3) := by
  have hs : ∀ i j, (g * (1 + nZero)) i j = ((1 + nZero) * g) i j := entry_comm_nZero h
  have e00 := hs 0 0
  have e01 := hs 0 1
  have e02 := hs 0 2
  have e03 := hs 0 3
  have e10 := hs 1 0
  have e12 := hs 1 2
  have e13 := hs 1 3
  have e22 := hs 2 2
  have e31 := hs 3 1
  have e32 := hs 3 2
  simp [nZero, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] at e00
  simp [nZero, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] at e01
  simp [nZero, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] at e02
  simp [nZero, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] at e03
  simp [nZero, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] at e10
  simp [nZero, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] at e12
  simp [nZero, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] at e13
  simp [nZero, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] at e22
  simp [nZero, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] at e31
  simp [nZero, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] at e32
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cMat]
  · exact e00
  · linear_combination -e01
  · linear_combination -e02
  · exact e03
  · exact e10
  · exact e22
  · linear_combination -e12 - e01
  · exact e13
  · exact e31
  · exact e32

theorem entry_of_eq {m m' : Mat4} (h : m = m') (i j : Fin 4) : m i j = m' i j :=
  congrFun (congrFun h i) j

theorem eq_o1Mat_of_comm {A : Mat4} (hu : A * p0Mat 1 0 0 = p0Mat 1 0 0 * A)
    (hv : A * p0Mat 0 1 0 = p0Mat 0 1 0 * A) :
    A = o1Mat (A 0 0) (A 0 1) (A 0 2) (A 0 3) := by
  have eu := entry_of_eq hu
  have ev := entry_of_eq hv
  have u00 := eu 0 0
  have u01 := eu 0 1
  have u02 := eu 0 2
  have u03 := eu 0 3
  have u10 := eu 1 0
  have u11 := eu 1 1
  have u12 := eu 1 2
  have u13 := eu 1 3
  have u20 := eu 2 0
  have u21 := eu 2 1
  have u22 := eu 2 2
  have u23 := eu 2 3
  have u30 := eu 3 0
  have u31 := eu 3 1
  have u32 := eu 3 2
  have u33 := eu 3 3
  have v00 := ev 0 0
  have v01 := ev 0 1
  have v02 := ev 0 2
  have v03 := ev 0 3
  have v10 := ev 1 0
  have v11 := ev 1 1
  have v12 := ev 1 2
  have v13 := ev 1 3
  have v20 := ev 2 0
  have v21 := ev 2 1
  have v22 := ev 2 2
  have v23 := ev 2 3
  have v30 := ev 3 0
  have v31 := ev 3 1
  have v32 := ev 3 2
  have v33 := ev 3 3
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at u00
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at u01
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at u02
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at u03
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at u10
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at u11
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at u12
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at u13
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at u20
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at u21
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at u22
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at u23
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at u30
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at u31
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at u32
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at u33
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at v00
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at v01
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at v02
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at v03
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at v10
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at v11
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at v12
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at v13
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at v20
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at v21
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at v22
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at v23
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at v30
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at v31
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at v32
  simp [p0Mat, Matrix.mul_apply, Fin.sum_univ_four] at v33
  ext i j
  fin_cases i <;> fin_cases j <;> simp [o1Mat]
  · exact u00
  · linear_combination -u01
  · exact u02
  · linear_combination -u03
  · exact u21
  · exact u23
  · linear_combination -v02
  · linear_combination -v03
  · exact u10
  · exact u33
  · exact u12
  · linear_combination -u13 - u01

theorem row_three_eq_zero_of_dual {A : Mat4} (hu : A * uDual = p0Mat 1 0 0 * A)
    (hv : A * vDual = p0Mat 0 1 0 * A) (hz : A * zDual = zMat * A) :
    A 3 0 = 0 ∧ A 3 1 = 0 ∧ A 3 2 = 0 ∧ A 3 3 = 0 := by
  have eu := entry_of_eq hu
  have ev := entry_of_eq hv
  have ez := entry_of_eq hz
  have u00 := eu 0 0
  have u01 := eu 0 1
  have u02 := eu 0 2
  have u03 := eu 0 3
  have u10 := eu 1 0
  have u11 := eu 1 1
  have u12 := eu 1 2
  have u13 := eu 1 3
  have u20 := eu 2 0
  have u21 := eu 2 1
  have u22 := eu 2 2
  have u23 := eu 2 3
  have u30 := eu 3 0
  have u31 := eu 3 1
  have u32 := eu 3 2
  have u33 := eu 3 3
  have v00 := ev 0 0
  have v01 := ev 0 1
  have v02 := ev 0 2
  have v03 := ev 0 3
  have v10 := ev 1 0
  have v11 := ev 1 1
  have v12 := ev 1 2
  have v13 := ev 1 3
  have v20 := ev 2 0
  have v21 := ev 2 1
  have v22 := ev 2 2
  have v23 := ev 2 3
  have v30 := ev 3 0
  have v31 := ev 3 1
  have v32 := ev 3 2
  have v33 := ev 3 3
  have z00 := ez 0 0
  have z01 := ez 0 1
  have z02 := ez 0 2
  have z03 := ez 0 3
  have z10 := ez 1 0
  have z11 := ez 1 1
  have z12 := ez 1 2
  have z13 := ez 1 3
  have z20 := ez 2 0
  have z21 := ez 2 1
  have z22 := ez 2 2
  have z23 := ez 2 3
  have z30 := ez 3 0
  have z31 := ez 3 1
  have z32 := ez 3 2
  have z33 := ez 3 3
  simp [p0Mat, uDual, Matrix.mul_apply, Fin.sum_univ_four] at u00
  simp [p0Mat, uDual, Matrix.mul_apply, Fin.sum_univ_four] at u01
  simp [p0Mat, uDual, Matrix.mul_apply, Fin.sum_univ_four] at u02
  simp [p0Mat, uDual, Matrix.mul_apply, Fin.sum_univ_four] at u03
  simp [p0Mat, uDual, Matrix.mul_apply, Fin.sum_univ_four] at u10
  simp [p0Mat, uDual, Matrix.mul_apply, Fin.sum_univ_four] at u11
  simp [p0Mat, uDual, Matrix.mul_apply, Fin.sum_univ_four] at u12
  simp [p0Mat, uDual, Matrix.mul_apply, Fin.sum_univ_four] at u13
  simp [p0Mat, uDual, Matrix.mul_apply, Fin.sum_univ_four] at u20
  simp [p0Mat, uDual, Matrix.mul_apply, Fin.sum_univ_four] at u21
  simp [p0Mat, uDual, Matrix.mul_apply, Fin.sum_univ_four] at u22
  simp [p0Mat, uDual, Matrix.mul_apply, Fin.sum_univ_four] at u23
  simp [p0Mat, uDual, Matrix.mul_apply, Fin.sum_univ_four] at u30
  simp [p0Mat, uDual, Matrix.mul_apply, Fin.sum_univ_four] at u31
  simp [p0Mat, uDual, Matrix.mul_apply, Fin.sum_univ_four] at u32
  simp [p0Mat, uDual, Matrix.mul_apply, Fin.sum_univ_four] at u33
  simp [p0Mat, vDual, Matrix.mul_apply, Fin.sum_univ_four] at v00
  simp [p0Mat, vDual, Matrix.mul_apply, Fin.sum_univ_four] at v01
  simp [p0Mat, vDual, Matrix.mul_apply, Fin.sum_univ_four] at v02
  simp [p0Mat, vDual, Matrix.mul_apply, Fin.sum_univ_four] at v03
  simp [p0Mat, vDual, Matrix.mul_apply, Fin.sum_univ_four] at v10
  simp [p0Mat, vDual, Matrix.mul_apply, Fin.sum_univ_four] at v11
  simp [p0Mat, vDual, Matrix.mul_apply, Fin.sum_univ_four] at v12
  simp [p0Mat, vDual, Matrix.mul_apply, Fin.sum_univ_four] at v13
  simp [p0Mat, vDual, Matrix.mul_apply, Fin.sum_univ_four] at v20
  simp [p0Mat, vDual, Matrix.mul_apply, Fin.sum_univ_four] at v21
  simp [p0Mat, vDual, Matrix.mul_apply, Fin.sum_univ_four] at v22
  simp [p0Mat, vDual, Matrix.mul_apply, Fin.sum_univ_four] at v23
  simp [p0Mat, vDual, Matrix.mul_apply, Fin.sum_univ_four] at v30
  simp [p0Mat, vDual, Matrix.mul_apply, Fin.sum_univ_four] at v31
  simp [p0Mat, vDual, Matrix.mul_apply, Fin.sum_univ_four] at v32
  simp [p0Mat, vDual, Matrix.mul_apply, Fin.sum_univ_four] at v33
  simp [zDual, zMat, rMat, Matrix.mul_apply, Fin.sum_univ_four] at z00
  simp [zDual, zMat, rMat, Matrix.mul_apply, Fin.sum_univ_four] at z01
  simp [zDual, zMat, rMat, Matrix.mul_apply, Fin.sum_univ_four] at z02
  simp [zDual, zMat, rMat, Matrix.mul_apply, Fin.sum_univ_four] at z03
  simp [zDual, zMat, rMat, Matrix.mul_apply, Fin.sum_univ_four] at z10
  simp [zDual, zMat, rMat, Matrix.mul_apply, Fin.sum_univ_four] at z11
  simp [zDual, zMat, rMat, Matrix.mul_apply, Fin.sum_univ_four] at z12
  simp [zDual, zMat, rMat, Matrix.mul_apply, Fin.sum_univ_four] at z13
  simp [zDual, zMat, rMat, Matrix.mul_apply, Fin.sum_univ_four] at z20
  simp [zDual, zMat, rMat, Matrix.mul_apply, Fin.sum_univ_four] at z21
  simp [zDual, zMat, rMat, Matrix.mul_apply, Fin.sum_univ_four] at z22
  simp [zDual, zMat, rMat, Matrix.mul_apply, Fin.sum_univ_four] at z23
  simp [zDual, zMat, rMat, Matrix.mul_apply, Fin.sum_univ_four] at z30
  simp [zDual, zMat, rMat, Matrix.mul_apply, Fin.sum_univ_four] at z31
  simp [zDual, zMat, rMat, Matrix.mul_apply, Fin.sum_univ_four] at z32
  simp [zDual, zMat, rMat, Matrix.mul_apply, Fin.sum_univ_four] at z33
  exact ⟨by linear_combination -2 * z00 - 2 * u10 + 2 * u01 + 2 * u03 - A 3 0 * three_eq_zero,
    z01, z02, z03⟩

theorem phiMat_u : phiMat (1, 0, 0) = p0Mat 1 0 0 := by decide

theorem phiMat_v : phiMat (0, 1, 0) = p0Mat 0 1 0 := by decide

theorem mul_dual_transpose :
    p0Mat 1 0 0 * uDualᵀ = 1 ∧ p0Mat 0 1 0 * vDualᵀ = 1 ∧ zMat * zDualᵀ = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem det_dual_transpose : uDualᵀ.det = 1 ∧ vDualᵀ.det = 1 ∧ zDualᵀ.det = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide
