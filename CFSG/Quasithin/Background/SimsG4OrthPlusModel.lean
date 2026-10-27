module

public import CFSG.Quasithin.Background.P3OrthoOm4
public import CFSG.Quasithin.Background.SimsG4OrthURefl

public section

open Matrix CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
  CFSG.Quasithin.G11.P3Ortho.Om4

namespace CFSG.Quasithin.SimsG4.OrthPlus

section Matrices

variable {K : Type} [Field K]

theorem polar_det_eq_trace (X Y : Matrix (Fin 2) (Fin 2) K) :
    QuadraticMap.polar (determinantForm K) X Y = (X * Y.adjugate).trace := by
  rw [determinantForm_polar, Matrix.adjugate_fin_two, Matrix.trace_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem adjugate_adjugate_two (X : Matrix (Fin 2) (Fin 2) K) : X.adjugate.adjugate = X := by
  rw [Matrix.adjugate_fin_two X, Matrix.adjugate_fin_two_of]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem adjugate_coe (s : Matrix.SpecialLinearGroup (Fin 2) K) :
    (s : Matrix (Fin 2) (Fin 2) K).adjugate = ((s⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) :=
  (Matrix.SpecialLinearGroup.coe_inv s).symm

theorem adjugate_coe_inv (s : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((s⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).adjugate =
      (s : Matrix (Fin 2) (Fin 2) K) := by
  rw [← adjugate_coe, adjugate_adjugate_two]

theorem trace_inv (s : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((s⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace =
      (s : Matrix (Fin 2) (Fin 2) K).trace := by
  rw [← adjugate_coe, Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [add_comm]

theorem trace_inv_mul (a b : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((a⁻¹ * b : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace =
      ((a * b⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace := by
  have h : a⁻¹ * b = (b⁻¹ * a)⁻¹ := by group
  rw [h, trace_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.trace_mul_comm]

variable [CharP K 2]

theorem refl_det_eq (s X : Matrix (Fin 2) (Fin 2) K) (hs : s.det = 1) :
    X + QuadraticMap.polar (determinantForm K) X s • s = s * X.adjugate * s := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [Matrix.det_fin_two] at hs
  rw [determinantForm_polar, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination X 0 0 * hs + X 0 0 * h2
  · linear_combination X 0 1 * hs + X 0 1 * h2
  · linear_combination X 1 0 * hs + X 1 0 * h2
  · linear_combination X 1 1 * hs + X 1 1 * h2

end Matrices

section Conj

variable {K : Type} [Field K] {W M : Type} [AddCommGroup W] [Module K W] [AddCommGroup M]
  [Module K M]

@[expose] def conjψ (ψ : W ≃ₗ[K] M) : (M ≃ₗ[K] M) ≃* (W ≃ₗ[K] W) where
  toFun g := ψ.trans (g.trans ψ.symm)
  invFun f := ψ.symm.trans (f.trans ψ)
  left_inv g := by ext; simp
  right_inv f := by ext; simp
  map_mul' g h := by ext; simp

theorem conjψ_symm_apply (ψ : W ≃ₗ[K] M) (f : W ≃ₗ[K] W) (X : M) :
    (conjψ ψ).symm f X = ψ (f (ψ.symm X)) := rfl

end Conj

section Rho

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]

theorem rho'_apply (z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)
    (X : Matrix (Fin 2) (Fin 2) K) :
    rho' K z X = (z.1 : Matrix (Fin 2) (Fin 2) K) * X *
      ((z.2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  specialRho_apply z X

@[expose] noncomputable def rhoW (ψ : W ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :
    Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →* (W ≃ₗ[K] W) :=
  (conjψ ψ).toMonoidHom.comp (rho' K)

variable (ψ : W ≃ₗ[K] Matrix (Fin 2) (Fin 2) K)

theorem apply_rhoW
    (z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) (w : W) :
    ψ (rhoW ψ z w) = (z.1 : Matrix (Fin 2) (Fin 2) K) * ψ w *
      ((z.2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  change ψ (ψ.symm (rho' K z (ψ w))) = _
  rw [LinearEquiv.apply_symm_apply, rho'_apply]

theorem rhoW_injective [CharP K 2] : Function.Injective (rhoW ψ) :=
  (conjψ ψ).injective.comp rho'_injective

variable {Q : QuadraticForm K W} (hψ : ∀ w, Q w = (ψ w).det)
include hψ

theorem rhoW_isometry
    (z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) (w : W) :
    Q (rhoW ψ z w) = Q w := by
  rw [hψ, hψ, apply_rhoW, Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe,
    Matrix.SpecialLinearGroup.det_coe, one_mul, mul_one]

theorem polar_eq (x y : W) :
    QuadraticMap.polar Q x y = QuadraticMap.polar (determinantForm K) (ψ x) (ψ y) := by
  simp only [QuadraticMap.polar, hψ, map_add, determinantForm_apply]

theorem polar_eq_trace {r r' : W} {s s' : Matrix.SpecialLinearGroup (Fin 2) K}
    (hr : ψ r = s) (hr' : ψ r' = s') :
    QuadraticMap.polar Q r r' =
      ((s * s'⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace := by
  rw [polar_eq ψ hψ, polar_det_eq_trace, hr, hr', adjugate_coe, Matrix.SpecialLinearGroup.coe_mul]

variable [CharP K 2]

theorem apply_reflK {r : W} {s : Matrix.SpecialLinearGroup (Fin 2) K} (hr : ψ r = s) (w : W) :
    ψ (reflK Q r w) = (s : Matrix (Fin 2) (Fin 2) K) * (ψ w).adjugate * s := by
  rw [reflK_apply, map_add, map_smul, polar_eq ψ hψ, hr]
  exact refl_det_eq _ _ (Matrix.SpecialLinearGroup.det_coe s)

theorem reflK_mul_reflK {r r' : W} {s s' : Matrix.SpecialLinearGroup (Fin 2) K} (hr : ψ r = s)
    (hr' : ψ r' = s') : reflK Q r * reflK Q r' = rhoW ψ (s * s'⁻¹, s⁻¹ * s') := by
  refine LinearEquiv.ext fun w => ψ.injective ?_
  rw [LinearEquiv.mul_apply, apply_reflK ψ hψ hr, apply_reflK ψ hψ hr', apply_rhoW]
  simp only [Matrix.adjugate_mul_distrib, adjugate_adjugate_two, adjugate_coe, _root_.mul_inv_rev,
    inv_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]

theorem reflK_mul_rhoW_mul_reflK {r : W} {s : Matrix.SpecialLinearGroup (Fin 2) K} (hr : ψ r = s)
    (z : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    reflK Q r * rhoW ψ z * reflK Q r = rhoW ψ (s * z.2 * s⁻¹, s⁻¹ * z.1 * s) := by
  refine LinearEquiv.ext fun w => ψ.injective ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, apply_reflK ψ hψ hr, apply_rhoW,
    apply_reflK ψ hψ hr, apply_rhoW]
  simp only [Matrix.adjugate_mul_distrib, adjugate_adjugate_two, adjugate_coe, adjugate_coe_inv,
    _root_.mul_inv_rev, inv_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]

theorem reflK_eq_rhoW_mul {r₀ r : W} (hr₀ : ψ r₀ = 1) {s : Matrix.SpecialLinearGroup (Fin 2) K}
    (hr : ψ r = s) : reflK Q r = rhoW ψ (s, s⁻¹) * reflK Q r₀ := by
  have h := reflK_mul_reflK ψ hψ hr (s' := 1) (by rw [hr₀, Matrix.SpecialLinearGroup.coe_one])
  rw [inv_one, mul_one, mul_one] at h
  rw [← h, mul_assoc, reflK_mul_self, mul_one]

theorem reflK_not_mem_range_rhoW {r : W} (hr : Q r = 1) : reflK Q r ∉ (rhoW ψ).range := by
  rintro ⟨z, hz⟩
  have hdet : (ψ r).det = 1 := by rw [← hψ, hr]
  set s : Matrix.SpecialLinearGroup (Fin 2) K := ⟨ψ r, hdet⟩
  have hs : ψ r = s := rfl
  set a : Matrix.SpecialLinearGroup (Fin 2) K := s⁻¹ * z.1
  set b : Matrix.SpecialLinearGroup (Fin 2) K := z.2⁻¹ * s⁻¹
  have hab : ∀ X : Matrix (Fin 2) (Fin 2) K,
      (a : Matrix (Fin 2) (Fin 2) K) * X * b = X.adjugate := by
    intro X
    have h := congrArg (fun f : W ≃ₗ[K] W => ψ (f (ψ.symm X))) hz
    simp only [apply_rhoW, apply_reflK ψ hψ hs, LinearEquiv.apply_symm_apply] at h
    have hss :
        ((s⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * s = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hss' : (s : Matrix (Fin 2) (Fin 2) K) * ((s⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc (a : Matrix (Fin 2) (Fin 2) K) * X * b
        = ((s⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
          ((z.1 : Matrix (Fin 2) (Fin 2) K) * X *
            ((z.2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
          ((s⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
          simp only [a, b, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]
      _ = ((s⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
          ((s : Matrix (Fin 2) (Fin 2) K) * X.adjugate * s) *
          ((s⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by rw [h]
      _ = X.adjugate := by
          simp only [← Matrix.mul_assoc, hss, Matrix.one_mul]
          rw [Matrix.mul_assoc, hss', Matrix.mul_one]
  have h1 : a * b = 1 := by
    apply Subtype.ext
    have := hab 1
    rw [Matrix.mul_one, Matrix.adjugate_one] at this
    rw [Matrix.SpecialLinearGroup.coe_mul, this, Matrix.SpecialLinearGroup.coe_one]
  have hba : b * a = 1 := by
    rw [← inv_eq_of_mul_eq_one_right h1, inv_mul_cancel]
  have h2 : (b : Matrix (Fin 2) (Fin 2) K) * a = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hba, Matrix.SpecialLinearGroup.coe_one]
  have hmul : ∀ X Y : Matrix (Fin 2) (Fin 2) K, (X * Y).adjugate = X.adjugate * Y.adjugate := by
    intro X Y
    rw [← hab, ← hab, ← hab]
    calc (a : Matrix (Fin 2) (Fin 2) K) * (X * Y) * b
        = (a : Matrix (Fin 2) (Fin 2) K) * X * ((b : Matrix (Fin 2) (Fin 2) K) * a) * Y * b := by
          rw [h2, Matrix.mul_one, Matrix.mul_assoc (a : Matrix (Fin 2) (Fin 2) K) X Y]
      _ = (a : Matrix (Fin 2) (Fin 2) K) * X * b * ((a : Matrix (Fin 2) (Fin 2) K) * Y * b) := by
          simp only [Matrix.mul_assoc]
  have h := congrFun (congrFun (hmul !![0, 1; 0, 0] !![0, 0; 1, 0]) 0) 0
  simp [Matrix.adjugate_fin_two] at h

end Rho

section Iso

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]

theorem exists_detCoords₀ {Q : QuadraticForm K W} (hdim : Module.finrank K W = 4)
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hplus : ∃ U : Submodule K W, Module.finrank K U = 2 ∧ ∀ u ∈ U, Q u = 0) :
    ∃ ψ : W ≃ₗ[K] Matrix (Fin 2) (Fin 2) K, ∀ w, Q w = (ψ w).det := by
  haveI : FiniteDimensional K W := Module.finite_of_finrank_pos (by rw [hdim]; norm_num)
  obtain ⟨U, hU, hUQ⟩ := hplus
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate :=
    ⟨fun x hx => hnd x hx, fun y hy => hnd y fun x => by
      rw [QuadraticMap.polar_comm]
      exact hy x⟩
  obtain ⟨φ⟩ := exists_determinant_isometry Q hQ hdim U hU hUQ
  exact ⟨φ.toLinearEquiv, fun w => by rw [← determinantForm_apply]; exact (φ.map_app w).symm⟩

theorem exists_detCoords {Q : QuadraticForm K W} (hdim : Module.finrank K W = 4)
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hplus : ∃ U : Submodule K W, Module.finrank K U = 2 ∧ ∀ u ∈ U, Q u = 0) {r₀ : W}
    (hr₀ : Q r₀ = 1) :
    ∃ ψ : W ≃ₗ[K] Matrix (Fin 2) (Fin 2) K, (∀ w, Q w = (ψ w).det) ∧ ψ r₀ = 1 := by
  obtain ⟨φ, hφ⟩ := exists_detCoords₀ hdim hnd hplus
  have hm : (φ r₀).det = 1 := by rw [← hφ, hr₀]
  set m : Matrix.SpecialLinearGroup (Fin 2) K := ⟨φ r₀, hm⟩
  refine ⟨φ.trans (rho' K (m⁻¹, 1)), fun w => ?_, ?_⟩
  · rw [LinearEquiv.trans_apply, rho'_apply, Matrix.det_mul, Matrix.det_mul,
      Matrix.SpecialLinearGroup.det_coe, Matrix.SpecialLinearGroup.det_coe, one_mul, mul_one]
    exact hφ w
  · rw [LinearEquiv.trans_apply, rho'_apply]
    change ((m⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * m *
      (((1 : Matrix.SpecialLinearGroup (Fin 2) K)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = 1
    rw [inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

variable (ψ : W ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) {Q : QuadraticForm K W}
  (hψ : ∀ w, Q w = (ψ w).det)
include hψ

theorem conjψ_symm_mem {g : W ≃ₗ[K] W} (hg : ∀ x, Q (g x) = Q x) :
    (conjψ ψ).symm g ∈ DeterminantIsometries K := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro X
  rw [determinantForm_apply, determinantForm_apply, conjψ_symm_apply, ← hψ, hg, hψ,
    LinearEquiv.apply_symm_apply]

theorem mem_range_rhoW_iff {g : W ≃ₗ[K] W} (hg : ∀ x, Q (g x) = Q x) :
    g ∈ (rhoW ψ).range ↔
      (⟨_, conjψ_symm_mem ψ hψ hg⟩ : DeterminantIsometries K) ∈ specialImage K := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, Subtype.ext ?_⟩
    change rho' K z = (conjψ ψ).symm g
    rw [← hz]
    exact ((conjψ ψ).symm_apply_apply _).symm
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have h := congrArg Subtype.val hz
    change rho' K z = (conjψ ψ).symm g at h
    change conjψ ψ (rho' K z) = g
    rw [h, MulEquiv.apply_symm_apply]

variable [Finite K] [CharP K 2]

theorem mem_range_rhoW_or_mul_reflK {r : W} (hr : Q r = 1) {g : W ≃ₗ[K] W}
    (hg : ∀ x, Q (g x) = Q x) : g ∈ (rhoW ψ).range ∨ g * reflK Q r ∈ (rhoW ψ).range := by
  have ht : ∀ x, Q (reflK Q r x) = Q x := reflK_isometry Q hr
  have hgt : ∀ x, Q ((g * reflK Q r) x) = Q x := fun x => by rw [LinearEquiv.mul_apply, hg, ht]
  rw [mem_range_rhoW_iff ψ hψ hg, mem_range_rhoW_iff ψ hψ hgt]
  set g' : DeterminantIsometries K := ⟨_, conjψ_symm_mem ψ hψ hg⟩
  set t' : DeterminantIsometries K := ⟨_, conjψ_symm_mem ψ hψ ht⟩
  have ht' : t' ∉ specialImage K := fun h =>
    reflK_not_mem_range_rhoW ψ hψ hr ((mem_range_rhoW_iff ψ hψ ht).mpr h)
  have htt : t' * tau ∈ specialImage K := (mem_specialImage_or_mul_tau t').resolve_left ht'
  have heq : (⟨_, conjψ_symm_mem ψ hψ hgt⟩ : DeterminantIsometries K) = g' * t' :=
    Subtype.ext (map_mul (conjψ ψ).symm g (reflK Q r))
  rw [heq]
  rcases mem_specialImage_or_mul_tau g' with h | h
  · exact Or.inl h
  · right
    have ht2 : t' * t' = 1 := Subtype.ext (by
      change (conjψ ψ).symm (reflK Q r) * (conjψ ψ).symm (reflK Q r) = 1
      rw [← map_mul, reflK_mul_self, map_one])
    have : g' * t' = g' * tau * (t' * tau)⁻¹ := by
      rw [_root_.mul_inv_rev, inv_eq_of_mul_eq_one_right ht2]
      group
    rw [this]
    exact (specialImage K).mul_mem h ((specialImage K).inv_mem htt)

end Iso

end CFSG.Quasithin.SimsG4.OrthPlus
