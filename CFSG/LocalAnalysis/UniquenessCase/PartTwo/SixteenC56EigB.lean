module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Diag

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open
open scoped Matrix MatrixGroups

namespace OmegaEig

variable {K : Type} [Field K]

@[expose] def IsHypQuad (e u f u' : OmI → K) : Prop :=
  quad e = 0 ∧ quad u = 0 ∧ quad f = 0 ∧ quad u' = 0 ∧ pol e f = 1 ∧ pol u u' = 1 ∧
    pol e u = 0 ∧ pol e u' = 0 ∧ pol f u = 0 ∧ pol f u' = 0

private def hypCol (e u f u' : OmI → K) : OmI → OmI → K :=
  Sum.elim ![e, u] ![f, u']

private def hypMat (e u f u' : OmI → K) : Matrix OmI OmI K :=
  Matrix.of fun i j => hypCol e u f u' j i

private theorem hypMat_col (e u f u' : OmI → K) (j : OmI) :
    (hypMat e u f u').col j = hypCol e u f u' j := rfl

private theorem hypMat_mulVec (e u f u' v : OmI → K) :
    hypMat e u f u' *ᵥ v = v (Sum.inl 0) • e + v (Sum.inl 1) • u +
      v (Sum.inr 0) • f + v (Sum.inr 1) • u' := by
  funext i
  rw [Matrix.mulVec_apply_eq_sum, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [hypMat, hypCol, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem quad_add4 (x y z w : OmI → K) :
    quad (x + y + z + w) =
      quad x + quad y + quad z + quad w +
        pol x y + pol x z + pol x w + pol y z + pol y w + pol z w := by
  rw [show x + y + z + w = (x + y) + (z + w) by abel]
  simp only [quad_add, pol_add_left, pol_add_right]
  ring

private theorem quad_smul_add4 (a b c d : K) (x y z w : OmI → K) :
    quad (a • x + b • y + c • z + d • w) =
      a ^ 2 * quad x + b ^ 2 * quad y + c ^ 2 * quad z + d ^ 2 * quad w +
        a * b * pol x y + a * c * pol x z + a * d * pol x w +
        b * c * pol y z + b * d * pol y w + c * d * pol z w := by
  rw [quad_add4]
  simp only [quad_smul, pol_smul_left, pol_smul_right]
  ring

theorem exists_isometry_of_isHypQuad {e u f u' : OmI → K} (h : IsHypQuad e u f u') :
    ∃ γ : GL OmI K, (∀ v, quad ((γ : Matrix OmI OmI K) *ᵥ v) = quad v) ∧
      (γ : Matrix OmI OmI K) *ᵥ Pi.single (Sum.inl 0) 1 = e ∧
      (γ : Matrix OmI OmI K) *ᵥ Pi.single (Sum.inl 1) 1 = u ∧
      (γ : Matrix OmI OmI K) *ᵥ Pi.single (Sum.inr 0) 1 = f ∧
      (γ : Matrix OmI OmI K) *ᵥ Pi.single (Sum.inr 1) 1 = u' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  have hiso : ∀ v : OmI → K, quad (hypMat e u f u' *ᵥ v) = quad v := by
    intro v
    rw [hypMat_mulVec, quad_smul_add4]
    have h9' : pol u f = 0 := by rw [pol_comm, h9]
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9', h10, quad_eq]
    ring
  have hpol : ∀ v w : OmI → K,
      pol (hypMat e u f u' *ᵥ v) (hypMat e u f u' *ᵥ w) = pol v w := by
    intro v w
    calc pol (hypMat e u f u' *ᵥ v) (hypMat e u f u' *ᵥ w)
        = quad (hypMat e u f u' *ᵥ v + hypMat e u f u' *ᵥ w) -
            quad (hypMat e u f u' *ᵥ v) - quad (hypMat e u f u' *ᵥ w) := rfl
      _ = quad (hypMat e u f u' *ᵥ (v + w)) -
            quad (hypMat e u f u' *ᵥ v) - quad (hypMat e u f u' *ᵥ w) := by
          rw [Matrix.mulVec_add]
      _ = quad (v + w) - quad v - quad w := by simp only [hiso]
      _ = pol v w := rfl
  have hker : ∀ v : OmI → K, hypMat e u f u' *ᵥ v = 0 → v = 0 := by
    intro v hv
    apply eq_zero_of_pol_eq_zero
    intro w
    rw [← hpol v w, hv]
    simp [pol_eq]
  have hinj : Function.Injective (hypMat e u f u').mulVec := by
    have hbot : LinearMap.ker (hypMat e u f u').mulVecLin = ⊥ :=
      Matrix.ker_mulVecLin_eq_bot_iff.mpr hker
    have h2' : Function.Injective (hypMat e u f u').mulVecLin := LinearMap.ker_eq_bot.mp hbot
    simpa only [Matrix.coe_mulVecLin] using h2'
  have hunit : IsUnit (hypMat e u f u') := Matrix.mulVec_injective_iff_isUnit.mp hinj
  let γ : GL OmI K := hunit.unit
  have hγ : (γ : Matrix OmI OmI K) = hypMat e u f u' := IsUnit.unit_spec hunit
  refine ⟨γ, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    rw [hγ]
    exact hiso v
  · rw [hγ, Matrix.mulVec_single_one, hypMat_col]
    rfl
  · rw [hγ, Matrix.mulVec_single_one, hypMat_col]
    rfl
  · rw [hγ, Matrix.mulVec_single_one, hypMat_col]
    rfl
  · rw [hγ, Matrix.mulVec_single_one, hypMat_col]
    rfl

theorem exists_singular_orth_not_mem [CharP K 2] {e₀ : OmI → K} (he₀ : e₀ ≠ 0) :
    ∃ s : OmI → K, quad s = 0 ∧ pol e₀ s = 0 ∧ ∀ t : K, s ≠ t • e₀ := by
  by_cases hx : e₀ (Sum.inl 0) = 0 ∧ e₀ (Sum.inl 1) = 0
  · refine ⟨Sum.elim ![e₀ (Sum.inr 1), e₀ (Sum.inr 0)] ![0, 0], ?_, ?_, ?_⟩
    · rw [quad_eq]
      simp
    · rw [pol_eq]
      simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
        hx.1, hx.2, mul_zero, zero_mul, add_zero, zero_add]
      rw [mul_comm (e₀ (Sum.inr 0)) (e₀ (Sum.inr 1))]
      exact CharTwo.add_self_eq_zero _
    · intro t ht
      have h1 := congrFun ht (Sum.inl 0)
      have h2 := congrFun ht (Sum.inl 1)
      simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.smul_apply, smul_eq_mul, hx.1, hx.2, mul_zero] at h1 h2
      exact he₀ (by
        funext i
        rcases i with i | i <;> fin_cases i <;> simp [hx.1, hx.2, h1, h2])
  · refine ⟨Sum.elim ![0, 0] ![e₀ (Sum.inl 1), e₀ (Sum.inl 0)], ?_, ?_, ?_⟩
    · rw [quad_eq]
      simp
    · rw [pol_eq]
      simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
        mul_zero, zero_mul, add_zero, zero_add]
      rw [mul_comm (e₀ (Sum.inl 1)) (e₀ (Sum.inl 0))]
      exact CharTwo.add_self_eq_zero _
    · intro t ht
      have h1 := congrFun ht (Sum.inl 0)
      have h2 := congrFun ht (Sum.inl 1)
      have h3 := congrFun ht (Sum.inr 0)
      have h4 := congrFun ht (Sum.inr 1)
      simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.smul_apply, smul_eq_mul] at h1 h2 h3 h4
      by_cases ht0 : t = 0
      · subst t
        simp only [zero_mul] at h3 h4
        exact hx ⟨h4, h3⟩
      · have hx1 : e₀ (Sum.inl 0) = 0 := by
          rcases mul_eq_zero.mp h1.symm with h | h
          · exact absurd h ht0
          · exact h
        have hx2 : e₀ (Sum.inl 1) = 0 := by
          rcases mul_eq_zero.mp h2.symm with h | h
          · exact absurd h ht0
          · exact h
        exact hx ⟨hx1, hx2⟩

end OmegaEig

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
