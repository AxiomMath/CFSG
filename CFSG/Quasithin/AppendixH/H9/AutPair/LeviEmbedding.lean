module

public import CFSG.Quasithin.AppendixH.H9.NaturalDualModel

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH.AutPair

variable {m : ℕ}

@[expose] def leviMat (B : Matrix (Fin m) (Fin m) (ZMod 2)) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2) :=
  Matrix.of fun i j =>
    Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => B i' j') j) i

@[simp] theorem leviMat_zero_zero (B : Matrix (Fin m) (Fin m) (ZMod 2)) : leviMat B 0 0 = 1 := by
  simp [leviMat]

@[simp] theorem leviMat_zero_succ (B : Matrix (Fin m) (Fin m) (ZMod 2)) (j : Fin m) :
    leviMat B 0 j.succ = 0 := by
  simp [leviMat]

@[simp] theorem leviMat_succ_zero (B : Matrix (Fin m) (Fin m) (ZMod 2)) (i : Fin m) :
    leviMat B i.succ 0 = 0 := by
  simp [leviMat]

@[simp] theorem leviMat_succ_succ (B : Matrix (Fin m) (Fin m) (ZMod 2)) (i j : Fin m) :
    leviMat B i.succ j.succ = B i j := by
  simp [leviMat]

theorem leviMat_one : leviMat (1 : Matrix (Fin m) (Fin m) (ZMod 2)) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · rw [leviMat_zero_zero, Matrix.one_apply_eq]
    · rw [leviMat_zero_succ, Matrix.one_apply_ne (Ne.symm (Fin.succ_ne_zero j))]
  · refine Fin.cases ?_ (fun j => ?_) j
    · rw [leviMat_succ_zero, Matrix.one_apply_ne (Fin.succ_ne_zero i)]
    · rw [leviMat_succ_succ, Matrix.one_apply, Matrix.one_apply]
      simp only [Fin.succ_inj]

theorem leviMat_mul (A B : Matrix (Fin m) (Fin m) (ZMod 2)) :
    leviMat (A * B) = leviMat A * leviMat B := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · rw [leviMat_zero_zero]
      conv_rhs => rw [Matrix.mul_apply, Fin.sum_univ_succ]
      simp
    · rw [leviMat_zero_succ]
      conv_rhs => rw [Matrix.mul_apply, Fin.sum_univ_succ]
      simp
  · refine Fin.cases ?_ (fun j => ?_) j
    · rw [leviMat_succ_zero]
      conv_rhs => rw [Matrix.mul_apply, Fin.sum_univ_succ]
      simp
    · rw [leviMat_succ_succ]
      conv_lhs => rw [Matrix.mul_apply]
      conv_rhs => rw [Matrix.mul_apply, Fin.sum_univ_succ]
      simp

theorem leviMat_transpose (B : Matrix (Fin m) (Fin m) (ZMod 2)) : (leviMat B)ᵀ = leviMat Bᵀ := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · rw [Matrix.transpose_apply, leviMat_zero_zero, leviMat_zero_zero]
    · rw [Matrix.transpose_apply, leviMat_succ_zero, leviMat_zero_succ]
  · refine Fin.cases ?_ (fun j => ?_) j
    · rw [Matrix.transpose_apply, leviMat_zero_succ, leviMat_succ_zero]
    · rw [Matrix.transpose_apply, leviMat_succ_succ, leviMat_succ_succ, Matrix.transpose_apply]

@[expose] def levi (m : ℕ) : GL (Fin m) (ZMod 2) →* GL (Fin (m + 1)) (ZMod 2) :=
  Units.map ⟨⟨leviMat, leviMat_one⟩, leviMat_mul⟩

theorem levi_val (B : GL (Fin m) (ZMod 2)) :
    ((levi m B : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) =
      leviMat (B : Matrix (Fin m) (Fin m) (ZMod 2)) := rfl

theorem levi_injective : Function.Injective (levi m) := by
  intro B B' h
  have hmat : leviMat (B : Matrix (Fin m) (Fin m) (ZMod 2)) =
      leviMat (B' : Matrix (Fin m) (Fin m) (ZMod 2)) := by
    have := congrArg (fun g : GL (Fin (m + 1)) (ZMod 2) =>
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2))) h
    simpa only [levi_val] using this
  apply Units.ext
  ext i j
  have := congrFun (congrFun hmat i.succ) j.succ
  simpa only [leviMat_succ_succ] using this

theorem dualGLn_levi (B : GL (Fin m) (ZMod 2)) :
    dualGLn (m + 1) (levi m B) = levi m (dualGLn m B) := by
  apply Units.ext
  show (((levi m B)⁻¹ : GL (Fin (m + 1)) (ZMod 2)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2))ᵀ =
    ((levi m (dualGLn m B) : GL (Fin (m + 1)) (ZMod 2)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2))
  rw [← map_inv, levi_val, levi_val, leviMat_transpose]
  rfl

theorem levi_mulVec_single (B : GL (Fin m) (ZMod 2)) :
    ((levi m B : GL (Fin (m + 1)) (ZMod 2)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ
      Pi.single 0 1 = Pi.single 0 1 := by
  rw [levi_val, Matrix.mulVec_single_one]
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [Matrix.col_apply, Pi.single_apply]
  · simp [Matrix.col_apply, Pi.single_apply, Fin.succ_ne_zero i]

theorem exists_eq_levi {A : GL (Fin (m + 1)) (ZMod 2)}
    (h₁ : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1)
    (h₂ : ((dualGLn (m + 1) A : GL (Fin (m + 1)) (ZMod 2)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    ∃ B : GL (Fin m) (ZMod 2), A = levi m B := by
  have hcol₁ : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)).col 0 = Pi.single 0 1 := by
    rw [← Matrix.mulVec_single_one]
    exact h₁
  have hA00 : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) 0 0 = 1 := by
    have := congrFun hcol₁ 0
    simpa [Matrix.col_apply, Pi.single_apply] using this
  have hAi0 : ∀ i : Fin m, (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) i.succ 0 = 0 := by
    intro i
    have := congrFun hcol₁ i.succ
    simpa [Matrix.col_apply, Pi.single_apply, Fin.succ_ne_zero i] using this
  have hcol₂ : ((dualGLn (m + 1) A : GL (Fin (m + 1)) (ZMod 2)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)).col 0 = Pi.single 0 1 := by
    rw [Matrix.mulVec_single_one] at h₂
    exact h₂
  have hAinv00 : ((A⁻¹ : GL (Fin (m + 1)) (ZMod 2)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) 0 0 = 1 := by
    have := congrFun hcol₂ 0
    simpa [dualGLn, Matrix.col_apply, Matrix.transpose_apply, Pi.single_apply] using this
  have hAinv0j : ∀ j : Fin m, ((A⁻¹ : GL (Fin (m + 1)) (ZMod 2)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) 0 j.succ = 0 := by
    intro j
    have := congrFun hcol₂ j.succ
    simpa [dualGLn, Matrix.col_apply, Matrix.transpose_apply, Pi.single_apply,
      Fin.succ_ne_zero j] using this
  have hAinvA : ((A⁻¹ : GL (Fin (m + 1)) (ZMod 2)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *
        (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) = 1 := by
    have := congrArg (fun g : GL (Fin (m + 1)) (ZMod 2) =>
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2))) (inv_mul_cancel A)
    simpa using this
  have hAAinv : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *
        ((A⁻¹ : GL (Fin (m + 1)) (ZMod 2)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) = 1 := by
    have := congrArg (fun g : GL (Fin (m + 1)) (ZMod 2) =>
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2))) (mul_inv_cancel A)
    simpa using this
  have hrow : ∀ j : Fin (m + 1),
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) 0 j =
        (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) 0 j := by
    intro j
    have h := congrFun (congrFun hAinvA 0) j
    rw [Matrix.mul_apply] at h
    rw [Fin.sum_univ_succ] at h
    have hsum : (∑ k : Fin m, ((A⁻¹ : GL (Fin (m + 1)) (ZMod 2)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) 0 k.succ *
          (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) k.succ j) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [hAinv0j k, zero_mul]
    rw [hAinv00, one_mul, hsum, add_zero] at h
    exact h
  have hA0j : ∀ j : Fin m, (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) 0 j.succ = 0 := by
    intro j
    have h := hrow j.succ
    rw [Matrix.one_apply_ne (show (0 : Fin (m + 1)) ≠ j.succ from
      fun hh => Fin.succ_ne_zero j hh.symm)] at h
    exact h
  refine ⟨{ val := Matrix.of fun i j =>
              (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) i.succ j.succ
            inv := Matrix.of fun i j =>
              ((A⁻¹ : GL (Fin (m + 1)) (ZMod 2)) :
                Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) i.succ j.succ
            val_inv := ?_
            inv_val := ?_ }, ?_⟩
  · ext i j
    have h := congrFun (congrFun hAAinv i.succ) j.succ
    rw [Matrix.mul_apply, Fin.sum_univ_succ, hAi0 i, zero_mul, zero_add] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [h]
    simp only [Matrix.one_apply, Fin.succ_inj]
  · ext i j
    have h := congrFun (congrFun hAinvA i.succ) j.succ
    rw [Matrix.mul_apply, Fin.sum_univ_succ, hA0j j, mul_zero, zero_add] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [h]
    simp only [Matrix.one_apply, Fin.succ_inj]
  · apply Units.ext
    rw [levi_val]
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · rw [hA00, leviMat_zero_zero]
      · rw [hA0j j, leviMat_zero_succ]
    · refine Fin.cases ?_ (fun j => ?_) j
      · rw [hAi0 i, leviMat_succ_zero]
      · rw [leviMat_succ_succ]
        rfl

end CFSG.ASVolI.ChH.AutPair
