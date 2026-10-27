module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerMatrixFixes

public section

open CFSG.Open CFSG.StandardType CFSG.StandardType.LieKnownR2.POmega.Radical
open CFSG.StandardType.ClassicalPosition
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal
open CFSG.ClassicalGroups.PCoreSection
open QuadraticMap
open Matrix
open CFSG.ComponentClassification.CatalogueBHigherLinearField

namespace CFSG.StandardType.LieKnownR2.POmega.Inner

theorem exists_conj_of_mem_spinAction_range {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {Q : QuadraticForm F (ι → F)} (hker : (spinAction Q).ker = ⊥)
    {T : (ι → F) ≃ₗ[F] (ι → F)} (hT : T ∈ (spinAction Q).range)
    {y : MulAut ↥(spinGroup Q)}
    (hact : ∀ x : ↥(spinGroup Q),
      spinAction Q (y x) = T * spinAction Q x * T⁻¹) :
    ∃ k : ↥(spinGroup Q), y = MulAut.conj k := by
  obtain ⟨k, hk⟩ := hT
  have hinj : Function.Injective (spinAction Q) :=
    (MonoidHom.ker_eq_bot_iff (spinAction Q)).mp hker
  refine ⟨k, MulEquiv.ext fun x => ?_⟩
  apply hinj
  rw [hact x, ← hk]
  change spinAction Q k * spinAction Q x * (spinAction Q k)⁻¹ =
    spinAction Q (k * x * k⁻¹)
  rw [map_mul, map_mul, map_inv]

private noncomputable def imat_glLin {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] :
    GL ι F →* ((ι → F) ≃ₗ[F] (ι → F)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F (ι → F)).toMonoidHom.comp
    Matrix.GeneralLinearGroup.toLin.toMonoidHom

private theorem imat_glLin_apply {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (g : GL ι F) (v : ι → F) : imat_glLin g v = (g : Matrix ι ι F) *ᵥ v := by
  simp [imat_glLin]

private theorem imat_glLin_spinMatrix {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (x : spinGroup Q) :
    imat_glLin (spinMatrix Q x) = spinAction Q x := by
  refine LinearEquiv.ext fun v => ?_
  rw [imat_glLin_apply, spinMatrix_mulVec]

private theorem imat_glFieldEquiv_refl {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (g : GL ι F) : glFieldEquiv ι (RingEquiv.refl F) g = g := by
  apply Units.ext
  ext i j
  exact glFieldEquiv_entry ι (RingEquiv.refl F) g i j

theorem exists_isometry_of_semilinear_frame {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] [CharP F 2] {Q : QuadraticForm F (ι → F)}
    {A : GL ι F} {φ : F ≃+* F} {μ : Fˣ} (hsim : GGSemilinearSimilitude Q A φ μ)
    (hφ : ∀ x : F, φ x = x) {y : MulAut ↥(spinGroup Q)}
    (hmat : GGMatrixSemilinearAction Q A φ μ y) :
    ∃ A' : (ι → F) ≃ₗ[F] (ι → F), (∀ v, Q (A' v) = Q v) ∧
      ∀ x : ↥(spinGroup Q), spinAction Q (y x) = A' * spinAction Q x * A'⁻¹ := by
  have hmat1 : GGMatrixSemilinearAction Q A (RingEquiv.refl F) μ y :=
    matrixAction_field_eq_one hφ hmat
  have hsim' : ∀ v, Q (A.val *ᵥ v) = (μ : F) * Q v := by
    intro v
    have hv := hsim v
    have hφv : (fun i => φ (v i)) = v := funext fun i => hφ (v i)
    rw [hφv, hφ] at hv
    exact hv
  obtain ⟨γ, A'₀, hA'₀, horth⟩ := exists_isometry_of_linear_similitude hsim'
  have hγ : (γ : F) ≠ 0 := Units.ne_zero γ
  have hA : A.val = (γ : F) • A'₀.val := by
    rw [hA'₀, smul_inv_smul₀ hγ]
  have hmat2 : GGMatrixSemilinearAction Q A'₀ (RingEquiv.refl F) 1 y :=
    (matrixAction_of_smul hγ hA).mp hmat1
  have hmatrix : ∀ x : ↥(spinGroup Q),
      spinMatrix Q (y x) = A'₀ * spinMatrix Q x * A'₀⁻¹ := by
    intro x
    have hx := hmat2 x
    rwa [imat_glFieldEquiv_refl] at hx
  refine ⟨imat_glLin A'₀, ?_, ?_⟩
  · intro v
    rw [imat_glLin_apply]
    exact horth v
  · intro x
    have hx := congrArg imat_glLin (hmatrix x)
    rw [map_mul, map_mul, map_inv, imat_glLin_spinMatrix, imat_glLin_spinMatrix] at hx
    exact hx

theorem ggRootNormInner_semilinear_frame {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] [CharP F 2] {Q : QuadraticForm F (ι → F)} (hS : SpinOmegaData Q)
    {P P' : HypPair Q} (h : P.Orth P') (hV : 6 ≤ Module.finrank F (ι → F))
    (hW : GGSiegelWIrreducible Q P P')
    {A : GL ι F} {φ : F ≃+* F} {μ : Fˣ} (hsim : GGSemilinearSimilitude Q A φ μ)
    (y : MulAut ↥(spinGroup Q)) (hy2 : ∃ k : ℕ, y ^ 2 ^ k = 1)
    (htriv : GGTrivialOnNormalizer (siegelRoot Q P.e P'.e) y)
    (hmat : GGMatrixSemilinearAction Q A φ μ y) :
    ∃ k : ↥(spinGroup Q), y = MulAut.conj k := by
  have hφ := fieldPart_eq_one_frame hS h hV hW hsim htriv hmat
  obtain ⟨A', hA', hact⟩ := exists_isometry_of_semilinear_frame hsim hφ hmat
  obtain ⟨hfix, hperp⟩ := isometry_fixes_siegelY_of_trivial hS h hV hW htriv hy2 hA' hact
  have hmem : A' ∈ (spinAction Q).range := by
    rw [hS.range_eq]
    exact ((axisRadical_le_axisParabolic (Q := Q) P P').trans
      (axisParabolic_le_elementaryGroup (Q := Q) P P'))
      (mem_axisRadical_of_flag hS.nondeg h hV hA' hfix hperp)
  exact exists_conj_of_mem_spinAction_range hS.ker_eq_bot hmem hact

end CFSG.StandardType.LieKnownR2.POmega.Inner
