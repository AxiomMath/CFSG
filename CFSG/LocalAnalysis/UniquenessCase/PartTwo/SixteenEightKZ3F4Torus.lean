module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3F4Model

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

noncomputable section

def s16kDUnit (i : Fin 3) : S16kGL6 where
  val := s16kBlockMat i
  inv := s16kBlockMat i * s16kBlockMat i
  val_inv := by
    fin_cases i <;>
      ext r c <;> fin_cases r <;> fin_cases c <;>
      simp only [Matrix.mul_apply, s16kBlockMat, Matrix.of_apply, Matrix.one_apply] <;>
      decide
  inv_val := by
    fin_cases i <;>
      ext r c <;> fin_cases r <;> fin_cases c <;>
      simp only [Matrix.mul_apply, s16kBlockMat, Matrix.of_apply, Matrix.one_apply] <;>
      decide

@[simp] theorem s16kDUnit_val (i : Fin 3) :
    ((s16kDUnit i : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = s16kBlockMat i := rfl

theorem s16kDUnit_mem (i : Fin 3) : s16kDUnit i ∈ s16kDiag :=
  Subgroup.subset_closure ⟨i, rfl⟩

private theorem s16k_theta_dunit_pow (i : Fin 3) :
    ∀ (k : ℕ) (v : Fin 6 → ZMod 2),
      s16kTheta
          (((s16kDUnit i ^ k : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v) =
        Function.update (s16kTheta v) i (s16kAlpha ^ k * s16kTheta v i) := by
  intro k
  induction k with
  | zero => intro v; simp
  | succ k ih =>
    intro v
    rw [pow_succ, Units.val_mul, ← Matrix.mulVec_mulVec, ih, s16kDUnit_val, s16kTheta_block,
      Function.update_idem, Function.update_self, pow_succ, mul_assoc]

private theorem s16k_theta_dunit_prod (a : Fin 3 → ℕ) (v : Fin 6 → ZMod 2) :
    s16kTheta
        (((s16kDUnit 0 ^ a 0 * s16kDUnit 1 ^ a 1 * s16kDUnit 2 ^ a 2 : S16kGL6) :
          Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v) =
      fun j => s16kAlpha ^ a j * s16kTheta v j := by
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec, s16k_theta_dunit_pow]
  funext j
  fin_cases j <;>
    simp [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
      show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

theorem s16k_mem_diag_of_theta (g : S16kGL6) (μ : Fin 3 → S16kF4)
    (hμ : ∀ i, μ i = 1 ∨ μ i = s16kAlpha ∨ μ i = s16kAlpha ^ 2)
    (hg : ∀ (v : Fin 6 → ZMod 2) (i : Fin 3),
      s16kTheta ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v) i = μ i * s16kTheta v i) :
    g ∈ s16kDiag := by
  have hex : ∀ i : Fin 3, ∃ k : ℕ, μ i = s16kAlpha ^ k := by
    intro i
    rcases hμ i with h | h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
    · exact ⟨2, by simp [h]⟩
  let a : Fin 3 → ℕ := fun i => (hex i).choose
  have ha : ∀ i, μ i = s16kAlpha ^ a i := fun i => (hex i).choose_spec
  set h : S16kGL6 := s16kDUnit 0 ^ a 0 * s16kDUnit 1 ^ a 1 * s16kDUnit 2 ^ a 2 with hh_def
  have hh : h ∈ s16kDiag := by
    rw [hh_def]
    exact mul_mem (mul_mem (pow_mem (s16kDUnit_mem 0) (a 0))
      (pow_mem (s16kDUnit_mem 1) (a 1))) (pow_mem (s16kDUnit_mem 2) (a 2))
  have hfun : ∀ v : Fin 6 → ZMod 2,
      (g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v =
        (h : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v := by
    intro v
    apply s16kTheta_bijective.1
    have hh_v : s16kTheta ((h : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v) =
        fun i => μ i * s16kTheta v i := by
      rw [hh_def, s16k_theta_dunit_prod a v]
      funext i
      rw [ha i]
    rw [funext (hg v), hh_v]
  have hgm : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      (h : Matrix (Fin 6) (Fin 6) (ZMod 2)) := Matrix.ext_iff_mulVec.2 hfun
  rw [Units.ext hgm]
  exact hh

end

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

