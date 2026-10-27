module

public import CFSG.Quasithin.AppendixH.H9.GLBasics
public import CFSG.Quasithin.AppendixH.H9.ModelBasic
public import CFSG.LargeExtraspecial.A2ModSLc
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

open scoped Matrix

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.ASVolI.ChH

private abbrev s168e3_e {m : ℕ} (i : Fin m) : Fin m → ZMod 2 := Pi.single i 1

private theorem s168e3_e_ne_zero {m : ℕ} (i : Fin m) : s168e3_e i ≠ 0 := by
  intro h
  have := congrFun h i
  simpa [s168e3_e] using this

private theorem s168e3_e_one_dot_e_zero {m : ℕ} [NeZero m] (hm : 2 ≤ m) :
    s168e3_e (1 : Fin m) ⬝ᵥ s168e3_e (0 : Fin m) = 0 := by
  have h10 : (1 : Fin m) ≠ 0 := by
    intro hc
    have h := congrArg Fin.val hc
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < m), Fin.val_zero] at h
    omega
  change Pi.single (1 : Fin m) (1 : ZMod 2) ⬝ᵥ Pi.single (0 : Fin m) (1 : ZMod 2) = 0
  rw [single_dotProduct, one_mul, Pi.single_eq_of_ne h10]

private theorem s168e3_e_zero_dot_e_zero {m : ℕ} [NeZero m] :
    s168e3_e (0 : Fin m) ⬝ᵥ s168e3_e (0 : Fin m) = 1 := by
  change Pi.single (0 : Fin m) (1 : ZMod 2) ⬝ᵥ Pi.single (0 : Fin m) (1 : ZMod 2) = 1
  rw [single_dotProduct, one_mul, Pi.single_eq_same]

private theorem s168e3_e_zero_ne_one {m : ℕ} [NeZero m] (hm : 2 ≤ m) :
    s168e3_e (0 : Fin m) ≠ s168e3_e (1 : Fin m) := by
  intro h
  have h0 : (Pi.single (0 : Fin m) (1 : ZMod 2) : Fin m → ZMod 2) 0 =
      (Pi.single (1 : Fin m) (1 : ZMod 2) : Fin m → ZMod 2) 0 := congrFun h (0 : Fin m)
  have h01 : (0 : Fin m) ≠ 1 := by
    intro hc
    have h := congrArg Fin.val hc
    rw [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < m)] at h
    omega
  rw [Pi.single_eq_same] at h0
  rw [Pi.single_eq_of_ne h01] at h0
  exact one_ne_zero h0

private theorem s168e3_orderOf_conj {m : ℕ} (A B : GL (Fin m) (ZMod 2)) :
    orderOf (A⁻¹ * B * A) = orderOf B := by
  have h : A⁻¹ * B * A = MulAut.conj A⁻¹ B := by
    rw [MulAut.conj_apply]
    group
  rw [h]
  exact MulEquiv.orderOf_eq (MulAut.conj A⁻¹) B

private theorem s168e3_conj_mulVec {m : ℕ} (A B : GL (Fin m) (ZMod 2))
    (x e : Fin m → ZMod 2)
    (hA : (A : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ x = e)
    (hB : (B : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ e = e) :
    (((A⁻¹ * B * A : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ x) = x := by
  rw [show (((A⁻¹ * B * A : GL (Fin m) (ZMod 2))) : Matrix (Fin m) (Fin m) (ZMod 2)) =
      ((A⁻¹ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) *
        (B : Matrix (Fin m) (Fin m) (ZMod 2)) *
        (A : Matrix (Fin m) (Fin m) (ZMod 2)) by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA, hB, ← hA]
  rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]

private theorem s168e3_conj_transpose_mulVec {m : ℕ} (A B : GL (Fin m) (ZMod 2))
    (w e : Fin m → ZMod 2)
    (hAw : (((dualGLn m A : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2))) *ᵥ w = e)
    (hB : (B : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ e = e)
    (hBsym : (B : Matrix (Fin m) (Fin m) (ZMod 2))ᵀ =
      (B : Matrix (Fin m) (Fin m) (ZMod 2))) :
    ((((A⁻¹ * B * A : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2))ᵀ) *ᵥ w) = w := by
  have hdual : ((dualGLn m A : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) =
      (((A⁻¹ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2))ᵀ) := rfl
  have hAt : (A : Matrix (Fin m) (Fin m) (ZMod 2))ᵀ *ᵥ e = w := by
    rw [← hAw, hdual, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
      ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.transpose_one, Matrix.one_mulVec]
  rw [show (((A⁻¹ * B * A : GL (Fin m) (ZMod 2))) : Matrix (Fin m) (Fin m) (ZMod 2))ᵀ =
      (A : Matrix (Fin m) (Fin m) (ZMod 2))ᵀ *
        (B : Matrix (Fin m) (Fin m) (ZMod 2))ᵀ *
        (((A⁻¹ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2))ᵀ) by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]]
  rw [← Matrix.mulVec_mulVec, ← hdual, hAw, hBsym, ← Matrix.mulVec_mulVec, hB, hAt]

private def s168e3_B4 : GL (Fin 4) (ZMod 2) where
  val := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]
  inv := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 1, 0]
  val_inv := by decide +kernel
  inv_val := by decide +kernel

private def s168e3_B5 : GL (Fin 5) (ZMod 2) where
  val := !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 1]
  inv := !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 1; 0, 0, 0, 1, 0]
  val_inv := by decide +kernel
  inv_val := by decide +kernel

private theorem s168e3_fix_two_of {m : ℕ} [NeZero m] (hm : 2 ≤ m) (B₀ : GL (Fin m) (ZMod 2))
    (hB₀ : orderOf B₀ = 3)
    (he₀ : (B₀ : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ s168e3_e (0 : Fin m) = s168e3_e 0)
    (he₁ : (B₀ : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ s168e3_e (1 : Fin m) = s168e3_e 1)
    (u v : Fin m → ZMod 2) :
    ∃ B : GL (Fin m) (ZMod 2), orderOf B = 3 ∧
      (B : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ u = u ∧
      (B : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ v = v := by
  by_cases hu : u = 0
  · subst hu
    by_cases hv : v = 0
    · subst hv
      exact ⟨B₀, hB₀, by simp, by simp⟩
    · obtain ⟨A, hA⟩ := exists_GL_mulVec_eq hv (s168e3_e_ne_zero 0)
      exact ⟨A⁻¹ * B₀ * A, by rw [s168e3_orderOf_conj]; exact hB₀, by simp,
        s168e3_conj_mulVec A B₀ v (s168e3_e 0) hA he₀⟩
  · by_cases hv : v = 0
    · subst hv
      obtain ⟨A, hA⟩ := exists_GL_mulVec_eq hu (s168e3_e_ne_zero 0)
      exact ⟨A⁻¹ * B₀ * A, by rw [s168e3_orderOf_conj]; exact hB₀,
        s168e3_conj_mulVec A B₀ u (s168e3_e 0) hA he₀, by simp⟩
    · by_cases huv : u = v
      · subst huv
        obtain ⟨A, hA⟩ := exists_GL_mulVec_eq hu (s168e3_e_ne_zero 0)
        exact ⟨A⁻¹ * B₀ * A, by rw [s168e3_orderOf_conj]; exact hB₀,
          s168e3_conj_mulVec A B₀ u (s168e3_e 0) hA he₀,
          s168e3_conj_mulVec A B₀ u (s168e3_e 0) hA he₀⟩
      · obtain ⟨g, hgu, hgv⟩ := CFSG.LargeExtraspecial.A2Mod.exists_mulVec_eq_pair hu hv
          (fun h => huv h.symm)
          (s168e3_e_ne_zero 0) (s168e3_e_ne_zero 1) (s168e3_e_zero_ne_one hm).symm
        let A : GL (Fin m) (ZMod 2) := Matrix.SpecialLinearGroup.toGL g
        have hA : (A : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ u = s168e3_e 0 := by
          rw [show (A : Matrix (Fin m) (Fin m) (ZMod 2)) =
            (g : Matrix (Fin m) (Fin m) (ZMod 2)) from
            Matrix.SpecialLinearGroup.coe_GL_coe_matrix g]
          exact hgu
        have hA' : (A : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ v = s168e3_e 1 := by
          rw [show (A : Matrix (Fin m) (Fin m) (ZMod 2)) =
            (g : Matrix (Fin m) (Fin m) (ZMod 2)) from
            Matrix.SpecialLinearGroup.coe_GL_coe_matrix g]
          exact hgv
        exact ⟨A⁻¹ * B₀ * A, by rw [s168e3_orderOf_conj]; exact hB₀,
          s168e3_conj_mulVec A B₀ u (s168e3_e 0) hA he₀,
          s168e3_conj_mulVec A B₀ v (s168e3_e 1) hA' he₁⟩

private theorem s168e3_fix_dual_of {m : ℕ} [NeZero m] (hm : 2 ≤ m) (B₀ : GL (Fin m) (ZMod 2))
    (hB₀ : orderOf B₀ = 3)
    (he₀ : (B₀ : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ s168e3_e (0 : Fin m) = s168e3_e 0)
    (he₁ : (B₀ : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ s168e3_e (1 : Fin m) = s168e3_e 1)
    (hsym : (B₀ : Matrix (Fin m) (Fin m) (ZMod 2))ᵀ =
      (B₀ : Matrix (Fin m) (Fin m) (ZMod 2)))
    (u w : Fin m → ZMod 2) :
    ∃ B : GL (Fin m) (ZMod 2), orderOf B = 3 ∧
      (B : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ u = u ∧
      ((B : Matrix (Fin m) (Fin m) (ZMod 2))ᵀ) *ᵥ w = w := by
  by_cases hu : u = 0
  · subst hu
    by_cases hw : w = 0
    · subst hw
      exact ⟨B₀, hB₀, by simp, by simp [hsym]⟩
    · obtain ⟨C, hC⟩ := exists_GL_mulVec_eq hw (s168e3_e_ne_zero 0)
      let A : GL (Fin m) (ZMod 2) := dualGLn m C
      have hA : ((dualGLn m A : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ w =
          s168e3_e 0 := by
        show ((dualGLn m (dualGLn m C) : GL (Fin m) (ZMod 2)) :
          Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ w = s168e3_e 0
        rw [dualGLn_dualGLn]
        exact hC
      exact ⟨A⁻¹ * B₀ * A, by rw [s168e3_orderOf_conj]; exact hB₀, by simp,
        s168e3_conj_transpose_mulVec A B₀ w (s168e3_e 0) hA he₀ hsym⟩
  · by_cases hw : w = 0
    · subst hw
      obtain ⟨A, hA⟩ := exists_GL_mulVec_eq hu (s168e3_e_ne_zero 0)
      exact ⟨A⁻¹ * B₀ * A, by rw [s168e3_orderOf_conj]; exact hB₀,
        s168e3_conj_mulVec A B₀ u (s168e3_e 0) hA he₀, by simp⟩
    · rcases CFSG.LargeExtraspecial.A2Mod.zmodTwo_eq_zero_or_one (w ⬝ᵥ u) with h0 | h1
      · obtain ⟨A, hAu, hAw⟩ := exists_GL_mulVec_pair hu hw (s168e3_e_ne_zero 0)
          (s168e3_e_ne_zero 1) (by rw [h0]; exact (s168e3_e_one_dot_e_zero hm).symm)
        have hA : ((dualGLn m A : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ w =
            s168e3_e 1 := hAw
        exact ⟨A⁻¹ * B₀ * A, by rw [s168e3_orderOf_conj]; exact hB₀,
          s168e3_conj_mulVec A B₀ u (s168e3_e 0) hAu he₀,
          s168e3_conj_transpose_mulVec A B₀ w (s168e3_e 1) hA he₁ hsym⟩
      · obtain ⟨A, hAu, hAw⟩ := exists_GL_mulVec_pair hu hw (s168e3_e_ne_zero 0)
          (s168e3_e_ne_zero 0) (by rw [h1]; exact (s168e3_e_zero_dot_e_zero).symm)
        have hA : ((dualGLn m A : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ w =
            s168e3_e 0 := hAw
        exact ⟨A⁻¹ * B₀ * A, by rw [s168e3_orderOf_conj]; exact hB₀,
          s168e3_conj_mulVec A B₀ u (s168e3_e 0) hAu he₀,
          s168e3_conj_transpose_mulVec A B₀ w (s168e3_e 0) hA he₀ hsym⟩

theorem s168e3_ln_fix_two {m : ℕ} (hm4 : 4 ≤ m) (hm5 : m ≤ 5) (u v : Fin m → ZMod 2) :
    ∃ B : GL (Fin m) (ZMod 2), orderOf B = 3 ∧
      (B : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ u = u ∧
      (B : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ v = v := by
  interval_cases m
  · exact s168e3_fix_two_of (by norm_num) s168e3_B4
      (orderOf_eq_prime (by decide +kernel) (by decide +kernel))
      (by decide +kernel) (by decide +kernel) u v
  · exact s168e3_fix_two_of (by norm_num) s168e3_B5
      (orderOf_eq_prime (by decide +kernel) (by decide +kernel))
      (by decide +kernel) (by decide +kernel) u v

theorem s168e3_ln_fix_dual {m : ℕ} (hm4 : 4 ≤ m) (hm5 : m ≤ 5) (u w : Fin m → ZMod 2) :
    ∃ B : GL (Fin m) (ZMod 2), orderOf B = 3 ∧
      (B : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ u = u ∧
      ((B : Matrix (Fin m) (Fin m) (ZMod 2))ᵀ) *ᵥ w = w := by
  interval_cases m
  · exact s168e3_fix_dual_of (by norm_num) s168e3_B4
      (orderOf_eq_prime (by decide +kernel) (by decide +kernel))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) u w
  · exact s168e3_fix_dual_of (by norm_num) s168e3_B5
      (orderOf_eq_prime (by decide +kernel) (by decide +kernel))
      (by decide +kernel) (by decide +kernel) (by decide +kernel) u w

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
