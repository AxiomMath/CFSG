module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.HeisenbergDefs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

public section

namespace CFSG.StandardType.ClassicalPosition.HeisRank

private def heisDesc_repHom {K F : Type} [Field K] [Field F] [Algebra K F] {N : ℕ}
    (E : Subgroup (GL (Fin N) K)) :
    E →* ((Fin N → F) ≃ₗ[F] (Fin N → F)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin N → F)).toMonoidHom.comp
    ((Matrix.GeneralLinearGroup.toLin).toMonoidHom.comp
      ((Matrix.GeneralLinearGroup.map (algebraMap K F)).comp E.subtype))

private lemma heisDesc_generalLinearEquiv_apply {R M : Type} [Semiring R] [AddCommMonoid M]
    [Module R M] (f : LinearMap.GeneralLinearGroup R M) (v : M) :
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R M f) v = (f : M →ₗ[R] M) v :=
  rfl

private lemma heisDesc_repHom_apply {K F : Type} [Field K] [Field F] [Algebra K F] {N : ℕ}
    (E : Subgroup (GL (Fin N) K)) (g : E) (v : Fin N → F) :
    heisDesc_repHom E g v
      = ((g.1 : Matrix (Fin N) (Fin N) K).map (algebraMap K F)).mulVec v := by
  simp only [heisDesc_repHom, MonoidHom.comp_apply]
  change ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin N → F))
      (Matrix.GeneralLinearGroup.toLin
        (Matrix.GeneralLinearGroup.map (algebraMap K F) g.1))) v = _
  rw [heisDesc_generalLinearEquiv_apply, Matrix.GeneralLinearGroup.toLin_apply,
    Matrix.mulVecLin_apply, Matrix.GeneralLinearGroup.val_map_apply]

private lemma heisDesc_mem_range_scalar_of_mulVec {K F : Type} [Field K] [Field F] [Algebra K F]
    {N : ℕ} (M : Matrix (Fin N) (Fin N) K) (c : F)
    (h : ∀ v : Fin N → F, (M.map (algebraMap K F)).mulVec v = c • v) :
    M ∈ Set.range (Matrix.scalar (Fin N)) := by
  by_cases hN : N = 0
  · subst hN
    exact ⟨0, Subsingleton.elim _ _⟩
  · have hcol : ∀ j : Fin N, (M.map (algebraMap K F)).col j = c • Pi.single j 1 := by
      intro j
      rw [← Matrix.mulVec_single_one]
      exact h (Pi.single j 1)
    have hentry : ∀ i j : Fin N,
        algebraMap K F (M i j) = c * (Pi.single j (1 : F) : Fin N → F) i := by
      intro i j
      have hh := congrFun (hcol j) i
      simpa [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] using hh
    have hdiag : ∀ i : Fin N, algebraMap K F (M i i) = c := by
      intro i
      simpa using hentry i i
    have hoff : ∀ i j : Fin N, i ≠ j → M i j = 0 := by
      intro i j hij
      apply (algebraMap K F).injective
      rw [map_zero]
      have hh := hentry i j
      rw [Pi.single_eq_of_ne hij, mul_zero] at hh
      exact hh
    have hdiag_eq : ∀ i j : Fin N, M i i = M j j := by
      intro i j
      apply (algebraMap K F).injective
      rw [hdiag i, hdiag j]
    have hi : 0 < N := Nat.pos_of_ne_zero hN
    let i₀ : Fin N := ⟨0, hi⟩
    refine ⟨M i₀ i₀, ?_⟩
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.scalar_apply, Matrix.diagonal_apply, if_pos rfl]
      exact hdiag_eq i₀ i
    · rw [Matrix.scalar_apply, Matrix.diagonal_apply, if_neg hij]
      exact (hoff i j hij).symm

theorem exists_rep_over {K F : Type} [Field K] [Field F] [Algebra K F] {N : ℕ}
    (E : Subgroup (GL (Fin N) K)) :
    ∃ φ : E →* ((Fin N → F) ≃ₗ[F] (Fin N → F)), Function.Injective φ ∧
      (scalarAut F (Fin N → F)).comap φ = (Subgroup.center (GL (Fin N) K)).subgroupOf E := by
  classical
  refine ⟨heisDesc_repHom E, ?_, ?_⟩
  · intro g h hgh
    have h1 : Matrix.GeneralLinearGroup.map (algebraMap K F) g.1
        = Matrix.GeneralLinearGroup.map (algebraMap K F) h.1 := by
      have h' := hgh
      simp only [heisDesc_repHom, MonoidHom.comp_apply] at h'
      have hto : Matrix.GeneralLinearGroup.toLin
            (Matrix.GeneralLinearGroup.map (algebraMap K F) g.1)
          = Matrix.GeneralLinearGroup.toLin
            (Matrix.GeneralLinearGroup.map (algebraMap K F) h.1) :=
        (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin N → F)).injective h'
      exact (Matrix.GeneralLinearGroup.toLin).injective hto
    have h2 : (g.1 : Matrix (Fin N) (Fin N) K).map (algebraMap K F)
        = (h.1 : Matrix (Fin N) (Fin N) K).map (algebraMap K F) := by
      have h'' := congrArg Units.val h1
      simpa [Matrix.GeneralLinearGroup.val_map_apply] using h''
    apply Subtype.ext
    apply Units.ext
    exact Matrix.map_injective (algebraMap K F).injective h2
  · ext g
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      rw [mem_scalarAut_iff] at hg
      obtain ⟨c, hc⟩ := hg
      rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
      exact heisDesc_mem_range_scalar_of_mulVec (g.1 : Matrix (Fin N) (Fin N) K) c fun v => by
        rw [← heisDesc_repHom_apply E g v]
        exact hc v
    · intro hg
      rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at hg
      obtain ⟨a, ha⟩ := hg
      rw [mem_scalarAut_iff]
      refine ⟨algebraMap K F a, fun v => ?_⟩
      rw [heisDesc_repHom_apply]
      have hmap : (g.1 : Matrix (Fin N) (Fin N) K).map (algebraMap K F)
          = Matrix.scalar (Fin N) (algebraMap K F a) := by
        rw [← ha]
        ext i j
        by_cases hij : i = j
        · subst hij
          simp [Matrix.scalar_apply, Matrix.diagonal_apply]
        · simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij]
      rw [hmap, Matrix.scalar_apply, Matrix.diagonal_const_mulVec]

end CFSG.StandardType.ClassicalPosition.HeisRank
