module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofSingerGen

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof

open Matrix CFSG.LieType.SeitzGeneration

variable {k : Type} [Field k] {ω : k}

@[expose] def m4_0 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![0, 1, 1; ω ^ 2, 0, 1; ω ^ 2, ω ^ 2, 0]

@[expose] def m4_1 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![0, 1, ω; ω, 0, ω ^ 2; 1, ω ^ 2, 0]

@[expose] def m4_2 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![0, 1, ω ^ 2; 1, 0, ω; ω, ω ^ 2, 0]

@[expose] def m4_3 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![1, ω, ω ^ 2; ω ^ 2, 1, 1; ω, 1, 1]

@[expose] def m4_4 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![ω, 1, 1; ω ^ 2, ω, 1; ω ^ 2, ω ^ 2, ω]

@[expose] def m4_5 (ω : k) : Matrix (Fin 3) (Fin 3) k :=
  !![ω ^ 2, ω ^ 2, ω ^ 2; 1, 0, 1; 1, ω ^ 2, ω ^ 2]

@[expose] def m4_6 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![ω, 1, ω ^ 2; ω, ω, ω ^ 2; ω, ω ^ 2, ω]

@[expose] def m4_7 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![0, 1, ω ^ 2; ω, ω, 0; ω ^ 2, ω, 0]

@[expose] def m4_8 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![1, 0, 0; ω, 1, 0; 0, 0, 1]

@[expose] def m4_9 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![1, 1, ω ^ 2; 1, 1, ω; ω, ω ^ 2, 1]

@[expose] def m4_10 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![ω ^ 2, ω, ω; 1, ω ^ 2, ω; 1, 1, ω ^ 2]

@[expose] def m4_11 (ω : k) : Matrix (Fin 3) (Fin 3) k :=
  !![ω ^ 2, ω ^ 2, ω; ω, 0, ω; ω ^ 2, ω ^ 2, ω ^ 2]

@[expose] def m4_12 (ω : k) : Matrix (Fin 3) (Fin 3) k :=
  !![ω ^ 2, ω, ω ^ 2; ω, ω ^ 2, ω ^ 2; ω, 1, ω ^ 2]

@[expose] def m4_13 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![0, ω ^ 2, ω; 0, ω ^ 2, ω ^ 2; ω, 1, 0]

@[expose] def m4_14 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![1, 0, 0; 0, 1, ω ^ 2; 0, 0, 1]

@[expose] def m4_15 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![0, 1, 1; ω, 0, 1; ω, ω, 0]

@[expose] def m4_16 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![0, 1, ω ^ 2; ω ^ 2, 0, ω; 1, ω, 0]

@[expose] def m4_17 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![0, 1, ω; 1, 0, ω ^ 2; ω ^ 2, ω, 0]

@[expose] def m4_18 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![1, ω ^ 2, ω; ω, 1, 1; ω ^ 2, 1, 1]

@[expose] def m4_19 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![ω ^ 2, 1, 1; ω, ω ^ 2, 1; ω, ω, ω ^ 2]

@[expose] def m4_20 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![ω, ω, ω; 1, 0, 1; 1, ω, ω]

@[expose] def m4_21 (ω : k) : Matrix (Fin 3) (Fin 3) k :=
  !![ω ^ 2, 1, ω; ω ^ 2, ω ^ 2, ω; ω ^ 2, ω, ω ^ 2]

@[expose] def m4_22 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![0, 1, ω; ω ^ 2, ω ^ 2, 0; ω, ω ^ 2, 0]

@[expose] def m4_23 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![1, 0, 0; ω ^ 2, 1, 0; 0, 0, 1]

@[expose] def m4_24 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![1, 1, ω; 1, 1, ω ^ 2; ω ^ 2, ω, 1]

@[expose] def m4_25 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![ω, ω ^ 2, ω ^ 2; 1, ω, ω ^ 2; 1, 1, ω]

@[expose] def m4_26 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![ω, ω, ω ^ 2; ω ^ 2, 0, ω ^ 2; ω, ω, ω]

@[expose] def m4_27 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![ω, ω ^ 2, ω; ω ^ 2, ω, ω; ω ^ 2, 1, ω]

@[expose] def m4_28 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![0, ω, ω ^ 2; 0, ω, ω; ω ^ 2, 1, 0]

@[expose] def m4_29 (ω : k) : Matrix (Fin 3) (Fin 3) k := !![1, 0, 0; 0, 1, ω; 0, 0, 1]

theorem m4_0_det (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) : (m4_0 ω).det = 1 := by
  simp [m4_0, Matrix.det_fin_three]; grind

theorem m4_0_comm_w_0 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    (heisC (ω)) * m4_0 ω = m4_0 ω * (heisC (ω)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_0, heisC, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_1_det (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) : (m4_1 ω).det = 1 := by
  simp [m4_1, Matrix.det_fin_three]; grind

theorem m4_1_comm_w_1 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    (heisD ω * heisC (ω)) * m4_1 ω = m4_1 ω * (heisD ω * heisC (ω)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_1, heisC, heisD, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_10_det (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) : (m4_10 ω).det = 1 := by
  simp [m4_10, Matrix.det_fin_three]; grind

theorem m4_10_comm_w_0 (h2 : (2 : k) = 0) (_hω : ω ^ 2 + ω + 1 = 0) :
    (heisC (ω)) * m4_10 ω = m4_10 ω * (heisC (ω)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_10, heisC, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals grind

theorem m4_15_det (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) : (m4_15 ω).det = 1 := by
  simp [m4_15, Matrix.det_fin_three]; grind

theorem m4_15_comm_w2_0 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    (heisC (ω ^ 2)) * m4_15 ω = m4_15 ω * (heisC (ω ^ 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_15, heisC, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_16_det (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) : (m4_16 ω).det = 1 := by
  simp [m4_16, Matrix.det_fin_three]; grind

theorem m4_16_comm_w2_2 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    (heisD ω * heisD ω * heisC (ω ^ 2)) * m4_16 ω =
      m4_16 ω * (heisD ω * heisD ω * heisC (ω ^ 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_16, heisC, heisD, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_17_det (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) : (m4_17 ω).det = 1 := by
  simp [m4_17, Matrix.det_fin_three]; grind

theorem m4_17_comm_w2_1 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    (heisD ω * heisC (ω ^ 2)) * m4_17 ω = m4_17 ω * (heisD ω * heisC (ω ^ 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_17, heisC, heisD, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_18_det (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) : (m4_18 ω).det = 1 := by
  simp [m4_18, Matrix.det_fin_three]; grind

theorem m4_18_comm_w2_2 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    (heisD ω * heisD ω * heisC (ω ^ 2)) * m4_18 ω =
      m4_18 ω * (heisD ω * heisD ω * heisC (ω ^ 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_18, heisC, heisD, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_19_det (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) : (m4_19 ω).det = 1 := by
  simp [m4_19, Matrix.det_fin_three]; grind

theorem m4_19_comm_w2_0 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    (heisC (ω ^ 2)) * m4_19 ω = m4_19 ω * (heisC (ω ^ 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_19, heisC, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_2_det (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) : (m4_2 ω).det = 1 := by
  simp [m4_2, Matrix.det_fin_three]; grind

theorem m4_2_comm_w_2 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    (heisD ω * heisD ω * heisC (ω)) * m4_2 ω = m4_2 ω * (heisD ω * heisD ω * heisC (ω)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_2, heisC, heisD, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_24_det (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) : (m4_24 ω).det = 1 := by
  simp [m4_24, Matrix.det_fin_three]; grind

theorem m4_24_comm_w2_1 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    (heisD ω * heisC (ω ^ 2)) * m4_24 ω = m4_24 ω * (heisD ω * heisC (ω ^ 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_24, heisC, heisD, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_25_det (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) : (m4_25 ω).det = 1 := by
  simp [m4_25, Matrix.det_fin_three]; grind

theorem m4_25_comm_w2_0 (h2 : (2 : k) = 0) (_hω : ω ^ 2 + ω + 1 = 0) :
    (heisC (ω ^ 2)) * m4_25 ω = m4_25 ω * (heisC (ω ^ 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_25, heisC, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals grind

theorem m4_3_det (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) : (m4_3 ω).det = 1 := by
  simp [m4_3, Matrix.det_fin_three]; grind

theorem m4_3_comm_w_1 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    (heisD ω * heisC (ω)) * m4_3 ω = m4_3 ω * (heisD ω * heisC (ω)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_3, heisC, heisD, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_4_det (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) : (m4_4 ω).det = 1 := by
  simp [m4_4, Matrix.det_fin_three]; grind

theorem m4_4_comm_w_0 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    (heisC (ω)) * m4_4 ω = m4_4 ω * (heisC (ω)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_4, heisC, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_9_det (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) : (m4_9 ω).det = 1 := by
  simp [m4_9, Matrix.det_fin_three]; grind

theorem m4_9_comm_w_2 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    (heisD ω * heisD ω * heisC (ω)) * m4_9 ω = m4_9 ω * (heisD ω * heisD ω * heisC (ω)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_9, heisC, heisD, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_0_mul_m4_1 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    m4_0 ω * m4_1 ω = m4_5 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_0, m4_1, m4_5, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_5_mul_m4_2 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    m4_5 ω * m4_2 ω = m4_6 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_5, m4_2, m4_6, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_6_mul_m4_3 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    m4_6 ω * m4_3 ω = m4_7 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_6, m4_3, m4_7, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_7_mul_m4_4 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    m4_7 ω * m4_4 ω = m4_8 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_7, m4_4, m4_8, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_0_mul_m4_2 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    m4_0 ω * m4_2 ω = m4_11 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_0, m4_2, m4_11, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_11_mul_m4_1 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    m4_11 ω * m4_1 ω = m4_12 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_11, m4_1, m4_12, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_12_mul_m4_9 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    m4_12 ω * m4_9 ω = m4_13 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_12, m4_9, m4_13, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_13_mul_m4_10 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    m4_13 ω * m4_10 ω = m4_14 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_13, m4_10, m4_14, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_15_mul_m4_16 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    m4_15 ω * m4_16 ω = m4_20 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_15, m4_16, m4_20, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_20_mul_m4_17 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    m4_20 ω * m4_17 ω = m4_21 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_20, m4_17, m4_21, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_21_mul_m4_18 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    m4_21 ω * m4_18 ω = m4_22 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_21, m4_18, m4_22, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_22_mul_m4_19 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    m4_22 ω * m4_19 ω = m4_23 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_22, m4_19, m4_23, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_15_mul_m4_17 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    m4_15 ω * m4_17 ω = m4_26 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_15, m4_17, m4_26, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_26_mul_m4_16 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    m4_26 ω * m4_16 ω = m4_27 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_26, m4_16, m4_27, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_27_mul_m4_24 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    m4_27 ω * m4_24 ω = m4_28 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_27, m4_24, m4_28, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m4_28_mul_m4_25 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) :
    m4_28 ω * m4_25 ω = m4_29 ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_28, m4_25, m4_29, Matrix.mul_apply, Fin.sum_univ_three] <;> grind


@[expose] def mkSL (A : Matrix (Fin 3) (Fin 3) k) (h : A.det = 1) : SpecialLinearGroup (Fin 3) k :=
  ⟨A, h⟩

theorem mem_of_five {K : Subgroup (SpecialLinearGroup (Fin 3) k)}
    {A₀ A₁ A₂ A₃ A₄ B₁ B₂ B₃ : Matrix (Fin 3) (Fin 3) k} {x : SpecialLinearGroup (Fin 3) k}
    (d₀ : A₀.det = 1) (d₁ : A₁.det = 1) (d₂ : A₂.det = 1) (d₃ : A₃.det = 1) (d₄ : A₄.det = 1)
    (k₀ : mkSL A₀ d₀ ∈ K) (k₁ : mkSL A₁ d₁ ∈ K) (k₂ : mkSL A₂ d₂ ∈ K) (k₃ : mkSL A₃ d₃ ∈ K)
    (k₄ : mkSL A₄ d₄ ∈ K)
    (p₁ : A₀ * A₁ = B₁) (p₂ : B₁ * A₂ = B₂) (p₃ : B₂ * A₃ = B₃)
    (p₄ : B₃ * A₄ = (x : Matrix (Fin 3) (Fin 3) k)) : x ∈ K := by
  have e : x = mkSL A₀ d₀ * mkSL A₁ d₁ * mkSL A₂ d₂ * mkSL A₃ d₃ * mkSL A₄ d₄ := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    exact (by rw [← p₄, ← p₃, ← p₂, ← p₁]; rfl)
  rw [e]
  exact K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem k₀ k₁) k₂) k₃) k₄

theorem m4_8_eq : m4_8 ω = ((xr (by decide : (1 : Fin 3) ≠ 0) ω :
    SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_8, xr, SpecialLinearGroup.transvection_coe]

theorem m4_14_eq : m4_14 ω = ((xr (by decide : (1 : Fin 3) ≠ 2) (ω ^ 2) :
    SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_14, xr, SpecialLinearGroup.transvection_coe]

theorem m4_23_eq : m4_23 ω = ((xr (by decide : (1 : Fin 3) ≠ 0) (ω ^ 2) :
    SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_23, xr, SpecialLinearGroup.transvection_coe]

theorem m4_29_eq : m4_29 ω = ((xr (by decide : (1 : Fin 3) ≠ 2) ω :
    SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m4_29, xr, SpecialLinearGroup.transvection_coe]

@[expose] def ToriIn (K : Subgroup (SpecialLinearGroup (Fin 3) k)) (ω α : k) : Prop :=
  (∀ y : SpecialLinearGroup (Fin 3) k,
      heisC α * (y : Matrix (Fin 3) (Fin 3) k) = (y : Matrix (Fin 3) (Fin 3) k) * heisC α →
        y ∈ K) ∧
    (∀ y : SpecialLinearGroup (Fin 3) k,
      (heisD ω * heisC α) * (y : Matrix (Fin 3) (Fin 3) k) =
        (y : Matrix (Fin 3) (Fin 3) k) * (heisD ω * heisC α) → y ∈ K) ∧
    ∀ y : SpecialLinearGroup (Fin 3) k,
      (heisD ω * heisD ω * heisC α) * (y : Matrix (Fin 3) (Fin 3) k) =
        (y : Matrix (Fin 3) (Fin 3) k) * (heisD ω * heisD ω * heisC α) → y ∈ K

theorem xr_mem_four_w (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0)
    {K : Subgroup (SpecialLinearGroup (Fin 3) k)} (hK : ToriIn K ω ω) :
    xr (by decide : (1 : Fin 3) ≠ 0) ω ∈ K ∧ xr (by decide : (1 : Fin 3) ≠ 2) (ω ^ 2) ∈ K := by
  obtain ⟨hK0, hK1, hK2⟩ := hK
  constructor
  · exact mem_of_five (m4_0_det h2 hω) (m4_1_det h2 hω) (m4_2_det h2 hω) (m4_3_det h2 hω)
      (m4_4_det h2 hω) (hK0 _ (m4_0_comm_w_0 h2 hω)) (hK1 _ (m4_1_comm_w_1 h2 hω))
      (hK2 _ (m4_2_comm_w_2 h2 hω)) (hK1 _ (m4_3_comm_w_1 h2 hω)) (hK0 _ (m4_4_comm_w_0 h2 hω))
      (m4_0_mul_m4_1 h2 hω) (m4_5_mul_m4_2 h2 hω) (m4_6_mul_m4_3 h2 hω)
      ((m4_7_mul_m4_4 h2 hω).trans m4_8_eq)
  · exact mem_of_five (m4_0_det h2 hω) (m4_2_det h2 hω) (m4_1_det h2 hω) (m4_9_det h2 hω)
      (m4_10_det h2 hω) (hK0 _ (m4_0_comm_w_0 h2 hω)) (hK2 _ (m4_2_comm_w_2 h2 hω))
      (hK1 _ (m4_1_comm_w_1 h2 hω)) (hK2 _ (m4_9_comm_w_2 h2 hω)) (hK0 _ (m4_10_comm_w_0 h2 hω))
      (m4_0_mul_m4_2 h2 hω) (m4_11_mul_m4_1 h2 hω) (m4_12_mul_m4_9 h2 hω)
      ((m4_13_mul_m4_10 h2 hω).trans m4_14_eq)

theorem xr_mem_four_w2 (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0)
    {K : Subgroup (SpecialLinearGroup (Fin 3) k)} (hK : ToriIn K ω (ω ^ 2)) :
    xr (by decide : (1 : Fin 3) ≠ 0) (ω ^ 2) ∈ K ∧ xr (by decide : (1 : Fin 3) ≠ 2) ω ∈ K := by
  obtain ⟨hK0, hK1, hK2⟩ := hK
  constructor
  · exact mem_of_five (m4_15_det h2 hω) (m4_16_det h2 hω) (m4_17_det h2 hω) (m4_18_det h2 hω)
      (m4_19_det h2 hω) (hK0 _ (m4_15_comm_w2_0 h2 hω)) (hK2 _ (m4_16_comm_w2_2 h2 hω))
      (hK1 _ (m4_17_comm_w2_1 h2 hω)) (hK2 _ (m4_18_comm_w2_2 h2 hω))
      (hK0 _ (m4_19_comm_w2_0 h2 hω))
      (m4_15_mul_m4_16 h2 hω) (m4_20_mul_m4_17 h2 hω) (m4_21_mul_m4_18 h2 hω)
      ((m4_22_mul_m4_19 h2 hω).trans m4_23_eq)
  · exact mem_of_five (m4_15_det h2 hω) (m4_17_det h2 hω) (m4_16_det h2 hω) (m4_24_det h2 hω)
      (m4_25_det h2 hω) (hK0 _ (m4_15_comm_w2_0 h2 hω)) (hK1 _ (m4_17_comm_w2_1 h2 hω))
      (hK2 _ (m4_16_comm_w2_2 h2 hω)) (hK1 _ (m4_24_comm_w2_1 h2 hω))
      (hK0 _ (m4_25_comm_w2_0 h2 hω))
      (m4_15_mul_m4_17 h2 hω) (m4_26_mul_m4_16 h2 hω) (m4_27_mul_m4_24 h2 hω)
      ((m4_28_mul_m4_25 h2 hω).trans m4_29_eq)

theorem eq_top_of_tori_four (h2 : (2 : k) = 0) (hω : ω ^ 2 + ω + 1 = 0) {α : k}
    (hα : α = ω ∨ α = ω ^ 2) {K : Subgroup (SpecialLinearGroup (Fin 3) k)}
    (hdiag : ∀ (a b d : k) (h : a * b * d = 1), diagSL a b d h ∈ K) (hK : ToriIn K ω α)
    {gα : GL (Fin 3) k} (hgα : (gα : Matrix (Fin 3) (Fin 3) k) = heisC α)
    (hinv : ∀ x ∈ K, conjUnit gα x ∈ K) : K = ⊤ := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  have hω20 : ω ^ 2 ≠ 0 := pow_ne_zero 2 hω0
  rcases hα with rfl | rfl
  · obtain ⟨h10, h12⟩ := xr_mem_four_w h2 hω hK
    exact eq_top_of_xr10_xr12 hω0 hgα hinv (xr10_mem_of_mem hdiag hω0 h10)
      (xr12_mem_of_mem hdiag hω20 h12)
  · obtain ⟨h10, h12⟩ := xr_mem_four_w2 h2 hω hK
    exact eq_top_of_xr10_xr12 hω20 hgα hinv (xr10_mem_of_mem hdiag hω20 h10)
      (xr12_mem_of_mem hdiag hω0 h12)

end CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof
