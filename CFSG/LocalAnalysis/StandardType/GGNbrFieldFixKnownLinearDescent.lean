module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQMat
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

public section

namespace CFSG.StandardType.LinearFieldFix

open CFSG.LocalAnalysis.GLTheoremA.FQ

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]

private noncomputable def sigmaAlgEquiv (σ : K ≃+* K) : K ≃ₐ[fixF σ] K :=
  AlgEquiv.ofRingEquiv (f := σ) fun x => by
    show σ (x : K) = (x : K)
    exact (mem_fixF (σ := σ)).mp x.2

private theorem smul_eq_of_eq_smul {M : Matrix ι ι K} (hM : M ≠ 0) {a b : K}
    (h : a • M = b • M) : a = b := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hM (by ext i j; exact h i j)
  have h' := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply] at h'
  exact mul_right_cancel₀ hij h'

private noncomputable def smulSubgroup (σ : K ≃+* K) (M : Matrix ι ι K) :
    Subgroup (K ≃ₐ[fixF σ] K) where
  carrier := {τ | ∃ u : Kˣ, M.map τ = (u : K) • M}
  one_mem' := by
    refine ⟨1, ?_⟩
    ext i j
    simp
  mul_mem' := by
    intro τ1 τ2 hτ1 hτ2
    obtain ⟨u1, h1⟩ := hτ1
    obtain ⟨u2, h2⟩ := hτ2
    refine ⟨Units.map τ1.toRingEquiv.toRingHom.toMonoidHom u2 * u1, ?_⟩
    ext i j
    have e1 := congrFun (congrFun h1 i) j
    have e2 := congrFun (congrFun h2 i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at e1 e2 ⊢
    calc (τ1 * τ2) (M i j)
        = τ1 (τ2 (M i j)) := AlgEquiv.mul_apply τ1 τ2 (M i j)
      _ = τ1 ((u2 : K) * M i j) := by rw [e2]
      _ = τ1 (u2 : K) * τ1 (M i j) :=
            map_mul τ1.toRingEquiv.toRingHom.toMonoidHom (u2 : K) (M i j)
      _ = τ1 (u2 : K) * ((u1 : K) * M i j) := by rw [e1]
      _ = (τ1 (u2 : K) * (u1 : K)) * M i j := by ring
      _ = ((Units.map τ1.toRingEquiv.toRingHom.toMonoidHom u2 * u1 : Kˣ) : K) * M i j := by
            rw [Units.val_mul, Units.coe_map]
            rfl
  inv_mem' := by
    rintro τ ⟨u, h⟩
    refine ⟨(Units.map τ.symm.toRingEquiv.toRingHom.toMonoidHom u)⁻¹, ?_⟩
    have hmap : (M.map τ).map τ.symm = M := by
      rw [Matrix.map_map]
      ext i j
      simp
    have hkey : ((u : K) • M).map τ.symm =
        (τ.symm (u : K)) • (M.map τ.symm) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
      exact map_mul τ.symm.toRingEquiv.toRingHom.toMonoidHom (u : K) (M i j)
    have hM : M = (τ.symm (u : K)) • (M.map τ.symm) := by
      rw [← hkey, ← h, hmap]
    have ha : τ.symm (u : K) ≠ 0 := by
      intro h0
      have h' : τ.symm (u : K) = τ.symm 0 := by rw [h0, map_zero]
      exact Units.ne_zero u (τ.symm.injective h')
    rw [Units.val_inv_eq_inv_val, Units.coe_map]
    change M.map τ.symm = (τ.symm (u : K))⁻¹ • M
    calc M.map τ.symm
        = (1 : K) • (M.map τ.symm) := (one_smul K _).symm
      _ = ((τ.symm (u : K))⁻¹ * τ.symm (u : K)) • (M.map τ.symm) := by
            rw [inv_mul_cancel₀ ha, one_smul]
      _ = (τ.symm (u : K))⁻¹ • ((τ.symm (u : K)) • (M.map τ.symm)) := by
            rw [smul_smul]
      _ = (τ.symm (u : K))⁻¹ • M := by rw [← hM]

private theorem zpowers_sigmaAlgEquiv_eq_top (σ : K ≃+* K) :
    Subgroup.zpowers (sigmaAlgEquiv σ) = ⊤ := by
  let S : Subgroup (K ≃ₐ[fixF σ] K) := Subgroup.zpowers (sigmaAlgEquiv σ)
  have hfix : IntermediateField.fixedField S = ⊥ := by
    ext x
    rw [IntermediateField.mem_fixedField_iff, IntermediateField.mem_bot,
      Subfield.algebraMap_ofSubfield, Set.mem_range]
    constructor
    · intro hx
      have hσx : σ x = x := by
        have h1 : sigmaAlgEquiv σ x = x := hx _ (Subgroup.mem_zpowers _)
        rw [sigmaAlgEquiv, AlgEquiv.ofRingEquiv_apply] at h1
        exact h1
      exact ⟨⟨x, hσx⟩, rfl⟩
    · rintro ⟨y, hy⟩ g hg
      rw [← hy]
      have hstab : sigmaAlgEquiv σ ∈
          MulAction.stabilizer (K ≃ₐ[fixF σ] K) (y : K) := by
        rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, sigmaAlgEquiv,
          AlgEquiv.ofRingEquiv_apply]
        exact y.2
      have hle : Subgroup.zpowers (sigmaAlgEquiv σ) ≤
          MulAction.stabilizer (K ≃ₐ[fixF σ] K) (y : K) :=
        Subgroup.zpowers_le.mpr hstab
      exact hle hg
  have h1 : S = IntermediateField.fixingSubgroup (IntermediateField.fixedField S) :=
    (IntermediateField.fixingSubgroup_fixedField S).symm
  rw [hfix] at h1
  show S = ⊤
  rw [h1, IntermediateField.fixingSubgroup_bot]

theorem exists_descend_of_map_eq_smul_matrix (σ : K ≃+* K) {M : Matrix ι ι K} (hM : M ≠ 0)
    {c : K} (hc : c ≠ 0) (h : M.map σ = c • M) :
    ∃ (μ : K) (N : Matrix ι ι (fixF σ)), μ ≠ 0 ∧ N.map (fixF σ).subtype = μ • M := by
  classical
  have hgen : Subgroup.zpowers (sigmaAlgEquiv σ) = ⊤ := zpowers_sigmaAlgEquiv_eq_top σ
  have hsig : sigmaAlgEquiv σ ∈ smulSubgroup σ M := by
    refine ⟨Units.mk0 c hc, ?_⟩
    change M.map σ = c • M
    exact h
  have hPtop : smulSubgroup σ M = ⊤ := by
    have hle : Subgroup.zpowers (sigmaAlgEquiv σ) ≤ smulSubgroup σ M :=
      Subgroup.zpowers_le.mpr hsig
    rw [hgen] at hle
    exact top_le_iff.mp hle
  have hmem : ∀ g : K ≃ₐ[fixF σ] K, ∃ u : Kˣ, M.map g = (u : K) • M := by
    intro g
    have hg : g ∈ smulSubgroup σ M := by rw [hPtop]; trivial
    exact hg
  let f : (K ≃ₐ[fixF σ] K) → Kˣ := fun g => Classical.choose (hmem g)
  have hf : ∀ g : K ≃ₐ[fixF σ] K, M.map g = (f g : K) • M :=
    fun g => Classical.choose_spec (hmem g)
  have hcocycle : groupCohomology.IsMulCocycle₁ f := by
    intro g h
    apply Units.ext
    apply smul_eq_of_eq_smul hM
    simp only [Units.val_mul, Units.coe_map, AlgEquiv.smul_units_def]
    rw [← hf (g * h)]
    calc M.map (g * h)
        = (M.map h).map g := by
            rw [Matrix.map_map]
            ext i j
            exact AlgEquiv.mul_apply g h (M i j)
      _ = ((f h : K) • M).map g := by rw [hf h]
      _ = (g (f h : K)) • (M.map g) := by
            ext i j
            simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
            exact map_mul g.toRingEquiv.toRingHom.toMonoidHom (f h : K) (M i j)
      _ = (g (f h : K)) • ((f g : K) • M) := by rw [hf g]
      _ = (g (f h : K) * (f g : K)) • M := by rw [smul_smul]
  obtain ⟨β, hβ⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hcocycle
  have hval : (f (sigmaAlgEquiv σ) : K) = c := by
    apply smul_eq_of_eq_smul hM
    rw [← hf (sigmaAlgEquiv σ)]
    change M.map σ = c • M
    exact h
  have hbeta : σ (β : K) = c * (β : K) := by
    have h1 : (sigmaAlgEquiv σ (β : K)) / (β : K) = c := by
      have h2 := congrArg (fun x : Kˣ => (x : K)) (hβ (sigmaAlgEquiv σ))
      rw [hval] at h2
      simpa using h2
    rw [div_eq_iff (Units.ne_zero β)] at h1
    rw [sigmaAlgEquiv, AlgEquiv.ofRingEquiv_apply] at h1
    exact h1
  let μ : K := (β : K)⁻¹
  have hμ : μ ≠ 0 := inv_ne_zero (Units.ne_zero β)
  let M' : Matrix ι ι K := μ • M
  have hσμc : σ μ * c = μ := by
    show σ ((β : K)⁻¹) * c = (β : K)⁻¹
    rw [map_inv₀, hbeta, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have hM'fix : M'.map σ = M' := by
    calc M'.map σ = (σ μ) • (M.map σ) := by
          show (μ • M).map σ = (σ μ) • (M.map σ)
          ext i j
          simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
          exact map_mul σ.toMonoidHom μ (M i j)
      _ = (σ μ) • (c • M) := by rw [h]
      _ = (σ μ * c) • M := by rw [smul_smul]
      _ = μ • M := by rw [hσμc]
      _ = M' := rfl
  let N : Matrix ι ι (fixF σ) := Matrix.of fun i j => ⟨M' i j, by
    have h1 := congrFun (congrFun hM'fix i) j
    simpa [Matrix.map_apply] using h1⟩
  have hN : N.map (fixF σ).subtype = μ • M := by
    ext i j
    rfl
  exact ⟨μ, N, hμ, hN⟩

theorem exists_descend_of_map_eq_smul [Nonempty ι] (σ : K ≃+* K) (A : GL ι K) (c : Kˣ)
    (h : ((Matrix.GeneralLinearGroup.map σ.toRingHom A : GL ι K) : Matrix ι ι K) =
      (c : K) • (A : Matrix ι ι K)) :
    ∃ (μ : Kˣ) (B : GL ι (fixF σ)),
      ((Matrix.GeneralLinearGroup.map (fixF σ).subtype B : GL ι K) : Matrix ι ι K) =
        (μ : K) • (A : Matrix ι ι K) := by
  classical
  have hM : (A : Matrix ι ι K) ≠ 0 := A.ne_zero
  have hc : (c : K) ≠ 0 := c.ne_zero
  have h' : (A : Matrix ι ι K).map σ = (c : K) • (A : Matrix ι ι K) := by
    have hh := h
    rw [CFSG.LocalAnalysis.GLTheoremA.YS09Field.coe_glMap σ.toRingHom A] at hh
    exact hh
  obtain ⟨μ, N, hμ, hN⟩ := exists_descend_of_map_eq_smul_matrix σ hM hc h'
  have hdet : N.det ≠ 0 := by
    intro h0
    have h1 : (fixF σ).subtype N.det = (μ • (A : Matrix ι ι K)).det := by
      rw [← hN]
      exact (RingHom.map_det (fixF σ).subtype N)
    rw [h0, map_zero, Matrix.det_smul] at h1
    have hAdet : (A : Matrix ι ι K).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero A
    exact (mul_ne_zero (pow_ne_zero _ hμ) hAdet) h1.symm
  let B : GL ι (fixF σ) := Matrix.GeneralLinearGroup.mkOfDetNeZero N hdet
  refine ⟨Units.mk0 μ hμ, B, ?_⟩
  have hB : (B : Matrix ι ι (fixF σ)) = N := rfl
  calc ((Matrix.GeneralLinearGroup.map (fixF σ).subtype B : GL ι K) : Matrix ι ι K)
      = (B : Matrix ι ι (fixF σ)).map (fixF σ).subtype := rfl
    _ = N.map (fixF σ).subtype := by rw [hB]
    _ = μ • (A : Matrix ι ι K) := hN
    _ = (Units.mk0 μ hμ : K) • (A : Matrix ι ι K) := rfl

end CFSG.StandardType.LinearFieldFix

end
