module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLPSL
public import CFSG.LocalAnalysis.StandardType.GGCoverRkFieldFix

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem scalar_mul_eq_smul_mat {d : ℕ} {K : Type} [Field K] (c : K)
    (M : Matrix (Fin d) (Fin d) K) : Matrix.scalar (Fin d) c * M = c • M := by
  ext i j
  rw [Matrix.scalar_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
  · intro h; exact absurd (Finset.mem_univ i) h

private theorem toGL_injective {d : ℕ} {K : Type} [Field K] :
    Function.Injective (fun u : SpecialLinearGroup (Fin d) K => SpecialLinearGroup.toGL u) := by
  intro u v h
  apply Subtype.ext
  have h2 := congrArg (fun z : GL (Fin d) K => (z : Matrix (Fin d) (Fin d) K)) h
  simpa only [SpecialLinearGroup.coe_GL_coe_matrix] using h2

private noncomputable def slOfDetOne {d : ℕ} {K : Type} [Field K] (u : GL (Fin d) K)
    (hu : Matrix.GeneralLinearGroup.det u = 1) : SpecialLinearGroup (Fin d) K :=
  ⟨(u : Matrix (Fin d) (Fin d) K), by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hu, Units.val_one]⟩

private theorem toGL_slOfDetOne {d : ℕ} {K : Type} [Field K] (u : GL (Fin d) K)
    (hu : Matrix.GeneralLinearGroup.det u = 1) :
    SpecialLinearGroup.toGL (slOfDetOne u hu) = u := by
  apply Units.ext
  rw [SpecialLinearGroup.coe_GL_coe_matrix]
  rfl

private theorem det_conj_map {d : ℕ} {K : Type} [Field K] (D : GL (Fin d) K) (σ : K ≃+* K)
    (x : SpecialLinearGroup (Fin d) K) :
    Matrix.GeneralLinearGroup.det
      (D * Matrix.GeneralLinearGroup.map σ.toRingHom (SpecialLinearGroup.toGL x) * D⁻¹) = 1 := by
  have hdetx : Matrix.GeneralLinearGroup.det (SpecialLinearGroup.toGL x) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.det_coe, Units.val_one]
  rw [map_mul, map_mul, map_inv, Matrix.GeneralLinearGroup.map_det, hdetx]
  simp

private noncomputable def wSL {d : ℕ} {K : Type} [Field K] (D : GL (Fin d) K) (σ : K ≃+* K)
    (x : SpecialLinearGroup (Fin d) K) : SpecialLinearGroup (Fin d) K :=
  slOfDetOne (D * Matrix.GeneralLinearGroup.map σ.toRingHom (SpecialLinearGroup.toGL x) * D⁻¹)
    (det_conj_map D σ x)

private theorem toGL_wSL {d : ℕ} {K : Type} [Field K] (D : GL (Fin d) K) (σ : K ≃+* K)
    (x : SpecialLinearGroup (Fin d) K) :
    SpecialLinearGroup.toGL (wSL D σ x) =
      D * Matrix.GeneralLinearGroup.map σ.toRingHom (SpecialLinearGroup.toGL x) * D⁻¹ :=
  toGL_slOfDetOne _ _

private theorem toGL_slConjugation {d : ℕ} {K : Type} [Field K] (D : GL (Fin d) K)
    (x : SpecialLinearGroup (Fin d) K) :
    SpecialLinearGroup.toGL
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d K D x) =
      D * SpecialLinearGroup.toGL x * D⁻¹ := by
  apply Units.ext
  rw [SpecialLinearGroup.coe_GL_coe_matrix, coe_slConjugation, Units.val_mul, Units.val_mul,
    SpecialLinearGroup.coe_GL_coe_matrix]

private theorem conj_scalar_mul {G : Type} [Group G] (s : G)
    (hs : ∀ N : G, s * N = N * s) (A : G) : s * A * s⁻¹ = A := by
  rw [hs A, mul_assoc, mul_inv_cancel, mul_one]

private theorem eq_of_on_sl {d : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    {φ : SpecialLinearGroup (Fin d) K →* L'} (hsurj : Function.Surjective φ)
    {f g : MulAut L'} (h : ∀ x, f (φ x) = g (φ x)) : f = g := by
  ext r
  obtain ⟨x, rfl⟩ := hsurj r
  exact h x

private theorem ratio_fixed_SL {d p m : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    {φ : SpecialLinearGroup (Fin d) K →* L'} (hd : 3 ≤ d)
    (hφk : ∀ g, φ g = 1 → g ∈ scalars d K) {σ : K ≃+* K} (hp : p.Prime)
    (hσ : σ ^ p ^ m = 1) {e : MulAut L'} (hep : e ^ p = 1) {t : Fin d → K}
    (ht : TypeANbrDvd.ActsDiag φ e t) :
    ∃ μ : K, μ ≠ 0 ∧ ∀ i, σ (t i) = μ * t i := by
  set i0 : Fin d := ⟨0, by omega⟩
  have hfix : ∀ i j, σ (t i * (t j)⁻¹) = t i * (t j)⁻¹ := fun i j =>
    fieldAut_fixes_pow_eq_one hp hσ (TypeANbrDvd.ActsDiag.ratio_pow hφk ht hep i j)
  have hσne : σ (t i0) ≠ 0 := by
    intro h0
    exact (ht.ne_zero i0) (σ.injective (by rw [h0, map_zero]))
  refine ⟨σ (t i0) * (t i0)⁻¹, ?_, ?_⟩
  · exact mul_ne_zero hσne (inv_ne_zero (ht.ne_zero i0))
  · intro i
    have hh := hfix i i0
    rw [map_mul, map_inv₀] at hh
    have h2 : σ (t i) = t i * (t i0)⁻¹ * σ (t i0) := by
      have h3 := congrArg (fun x => x * σ (t i0)) hh
      rw [mul_assoc] at h3
      rwa [inv_mul_cancel₀ hσne, mul_one] at h3
    rw [h2]
    ring

theorem exists_rho_commute_diag_SL {d p : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime)
    (hd : 3 ≤ d)
    {φ : SpecialLinearGroup (Fin d) K →* projectiveSL d K} (hφs : Function.Surjective φ)
    (hφk : ∀ g, φ g = 1 → g ∈ scalars d K) {σ : K ≃+* K} {m : ℕ} (hσ : σ ^ p ^ m = 1)
    {g : GL (Fin d) K} {a : MulAut (projectiveSL d K)}
    (ha : ∀ x y : SpecialLinearGroup (Fin d) K,
      SpecialLinearGroup.toGL y =
        g * Matrix.GeneralLinearGroup.map σ.toRingHom (SpecialLinearGroup.toGL x) * g⁻¹ →
      a (φ x) = φ y) :
    ∃ ρ : projectiveSL d K, ∀ e : MulAut (projectiveSL d K), e ^ p = 1 →
      (∃ t : Fin d → K, TypeANbrDvd.ActsDiag φ e t) → Commute ((MulAut.conj ρ)⁻¹ * a) e := by
  classical
  set i0 : Fin d := ⟨0, by omega⟩
  set δ : Kˣ := Matrix.GeneralLinearGroup.det g with hδ
  set eD : Fin d → K := fun i => if i = i0 then (δ : K) else 1 with heD
  have hdetD : (Matrix.diagonal eD).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    rw [Finset.prod_eq_single i0]
    · simpa [heD] using Units.ne_zero δ
    · intro b _ hb; simp [heD, hb]
    · intro h; exact absurd (Finset.mem_univ i0) h
  set D : GL (Fin d) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal eD) hdetD with hDdef
  have hDmat : (D : Matrix (Fin d) (Fin d) K) = diagonal eD :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _
  have hdetD_eq : Matrix.GeneralLinearGroup.det D = Units.mk0 (δ : K) (Units.ne_zero δ) := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hDmat, Matrix.det_diagonal]
    rw [Finset.prod_eq_single i0]
    · simp [heD]
    · intro b _ hb; simp [heD, hb]
    · intro h; exact absurd (Finset.mem_univ i0) h
  have hdet_s0 : Matrix.GeneralLinearGroup.det (g * D⁻¹) = 1 := by
    have hδ' : Matrix.GeneralLinearGroup.det g = δ := hδ.symm
    rw [map_mul, map_inv, hdetD_eq, hδ']
    rw [show Units.mk0 (δ : K) (Units.ne_zero δ) = δ from Units.ext rfl, mul_inv_cancel]
  set s₀ : SpecialLinearGroup (Fin d) K := slOfDetOne (g * D⁻¹) hdet_s0 with hs0def
  have htoGLs0 : SpecialLinearGroup.toGL s₀ = g * D⁻¹ := by
    rw [hs0def, toGL_slOfDetOne]
  refine ⟨φ s₀, fun e hep ht => ?_⟩
  obtain ⟨t, ht⟩ := ht
  obtain ⟨μ, hμne, hμt⟩ := ratio_fixed_SL hd hφk hp hσ hep ht
  obtain ⟨E, hEmat, hactE⟩ := ht
  set s : GL (Fin d) K := Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 μ hμne) with hsdef
  have hcent : ∀ N : GL (Fin d) K, s * N = N * s :=
    fun N => (Subgroup.mem_center_iff.mp (TableB.scalar_mem_center (Units.mk0 μ hμne)) N).symm
  have hσE : Matrix.GeneralLinearGroup.map σ.toRingHom E = s * E := by
    rw [hsdef]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_map_apply σ.toRingHom E, hEmat,
      Matrix.diagonal_map (map_zero σ.toRingHom)]
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, hEmat, scalar_mul_eq_smul_mat,
      ← Matrix.diagonal_smul]
    congr 1
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    change σ (t i) = (Units.mk0 μ hμne : K) * t i
    rw [hμt i, Units.val_mk0]
  have hDE : D * E = E * D := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hDmat, hEmat, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm (eD i) (t i)
  have hb : ∀ x : SpecialLinearGroup (Fin d) K,
      ((MulAut.conj (φ s₀))⁻¹ * a) (φ x) = φ (wSL D σ x) := by
    intro x
    have hconj : (MulAut.conj (φ s₀))⁻¹ = MulAut.conj ((φ s₀)⁻¹) := by
      ext z; simp [MulAut.conj_apply]
    have hy : SpecialLinearGroup.toGL (s₀ * wSL D σ x * s₀⁻¹) =
        g * Matrix.GeneralLinearGroup.map σ.toRingHom (SpecialLinearGroup.toGL x) * g⁻¹ := by
      rw [map_mul, map_mul, map_inv, htoGLs0, toGL_wSL D σ x]
      group
    have hax := ha x (s₀ * wSL D σ x * s₀⁻¹) hy
    rw [MulAut.mul_apply, hax, hconj, MulAut.conj_apply, inv_inv, ← map_inv, ← map_mul,
      ← map_mul]
    congr 1
    group
  apply eq_of_on_sl hφs
  intro x
  change ((MulAut.conj (φ s₀))⁻¹ * a) (e (φ x)) =
    e (((MulAut.conj (φ s₀))⁻¹ * a) (φ x))
  rw [hactE x, hb (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d K E x),
    hb x, hactE (wSL D σ x)]
  have hgoal : wSL D σ (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d K E x) =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d K E (wSL D σ x) := by
    apply toGL_injective
    change SpecialLinearGroup.toGL
        (wSL D σ (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d K E x)) =
      SpecialLinearGroup.toGL
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d K E (wSL D σ x))
    rw [toGL_wSL D σ (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d K E x),
      toGL_slConjugation E (wSL D σ x), toGL_wSL D σ x]
    rw [toGL_slConjugation E x]
    rw [map_mul, map_mul, map_inv, hσE]
    rw [show (s * E) * Matrix.GeneralLinearGroup.map σ.toRingHom (SpecialLinearGroup.toGL x) *
          (s * E)⁻¹ =
          s * (E * Matrix.GeneralLinearGroup.map σ.toRingHom (SpecialLinearGroup.toGL x) * E⁻¹) *
            s⁻¹ by group]
    rw [conj_scalar_mul s hcent]
    rw [show D * (E * Matrix.GeneralLinearGroup.map σ.toRingHom (SpecialLinearGroup.toGL x) * E⁻¹) *
            D⁻¹ = (D * E) * Matrix.GeneralLinearGroup.map σ.toRingHom (SpecialLinearGroup.toGL x) *
              (D * E)⁻¹ by group,
      show E * (D * Matrix.GeneralLinearGroup.map σ.toRingHom (SpecialLinearGroup.toGL x) * D⁻¹) *
            E⁻¹ = (E * D) * Matrix.GeneralLinearGroup.map σ.toRingHom (SpecialLinearGroup.toGL x) *
              (E * D)⁻¹ by group,
      hDE]
  rw [hgoal]

end CFSG.StandardType
