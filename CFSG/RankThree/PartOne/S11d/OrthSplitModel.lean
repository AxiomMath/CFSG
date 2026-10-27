module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageSplit

public section

namespace CFSG.RankThree.PartOne

open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

section Model

variable {K : Type} [Field K]

theorem inverseTranspose_mul (A B : Matrix.GeneralLinearGroup (Fin 2) K) :
    inverseTranspose (A * B) = inverseTranspose A * inverseTranspose B := by
  apply Units.ext
  change ((A * B)⁻¹).val.transpose = (A⁻¹).val.transpose * (B⁻¹).val.transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

omit [Field K] in
theorem units_eq_one_of_sq {F : Type} [Field F] [CharP F 2] {c : Fˣ} (h : c ^ 2 = 1) : c = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hc : (c : F) ^ 2 = 1 := by
    have := congrArg Units.val h
    simpa using this
  have h0 : ((c : F) - 1) ^ 2 = 0 := by linear_combination hc - (c : F) * h2 + h2
  have := (pow_eq_zero_iff two_ne_zero |>.mp h0)
  exact Units.ext (sub_eq_zero.mp this)

theorem specialRho_injective [CharP K 2] : Function.Injective (specialRho (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  obtain ⟨c, hc2, h1, h2⟩ := (specialRho_eq_one_iff z).mp hz
  have hc : c = 1 := units_eq_one_of_sq hc2
  subst hc
  rw [map_one] at h1 h2
  exact Prod.ext (Matrix.SpecialLinearGroup.toGL_injective (by rw [h1]; simp))
    (Matrix.SpecialLinearGroup.toGL_injective (by rw [h2]; simp))

theorem rho_mem_specialImage_char2 [Finite K] [CharP K 2] (z : equalDeterminants K) :
    rho z ∈ specialImage K := by
  obtain ⟨c₀, hc₀⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2)
    (commonDeterminant z : K)
  have hc0 : c₀ ≠ 0 := by
    rintro rfl
    exact (commonDeterminant z).ne_zero (by rw [hc₀]; ring)
  exact rho_mem_specialImage_of_commonDeterminant_eq_sq z (c := Units.mk0 c₀ hc0)
    (Units.ext (by simp [sq, hc₀]))

theorem exists_swap [Finite K] [CharP K 2] {ζ : DeterminantIsometries K} (hζ : ζ ∉ specialImage K) :
    ∃ z₁ z₂ : Matrix.GeneralLinearGroup (Fin 2) K, ∀ A B : SL(2, K), ∃ A' B' : SL(2, K),
      Matrix.SpecialLinearGroup.toGL A' =
        z₁ * inverseTranspose (Matrix.SpecialLinearGroup.toGL B) * z₁⁻¹ ∧
      Matrix.SpecialLinearGroup.toGL B' =
        z₂ * inverseTranspose (Matrix.SpecialLinearGroup.toGL A) * z₂⁻¹ ∧
      ζ * specialRho (A, B) * ζ⁻¹ = specialRho (A', B') := by
  obtain ⟨z, hz | hz⟩ := determinant_isometry_exhaustion ζ
  · exact absurd (hz ▸ rho_mem_specialImage_char2 z) hζ
  · refine ⟨z.val.1, z.val.2, fun A B => ?_⟩
    have hdet : ∀ (z₀ : Matrix.GeneralLinearGroup (Fin 2) K) (C : SL(2, K)),
        (z₀ * inverseTranspose (Matrix.SpecialLinearGroup.toGL C) * z₀⁻¹).val.det = 1 := by
      intro z₀ C
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
      have h1 : (inverseTranspose (Matrix.SpecialLinearGroup.toGL C)).val.det = 1 := by
        have := congrArg Units.val (inverseTranspose_det (Matrix.SpecialLinearGroup.toGL C))
        simpa using this
      rw [h1, mul_one, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.det_one]
    let A' : SL(2, K) := ⟨(z.val.1 * inverseTranspose (Matrix.SpecialLinearGroup.toGL B) *
      z.val.1⁻¹).val, hdet _ B⟩
    let B' : SL(2, K) := ⟨(z.val.2 * inverseTranspose (Matrix.SpecialLinearGroup.toGL A) *
      z.val.2⁻¹).val, hdet _ A⟩
    have hA' : Matrix.SpecialLinearGroup.toGL A' =
        z.val.1 * inverseTranspose (Matrix.SpecialLinearGroup.toGL B) * z.val.1⁻¹ :=
      Units.ext rfl
    have hB' : Matrix.SpecialLinearGroup.toGL B' =
        z.val.2 * inverseTranspose (Matrix.SpecialLinearGroup.toGL A) * z.val.2⁻¹ :=
      Units.ext rfl
    refine ⟨A', B', hA', hB', ?_⟩
    have hζ' : ζ⁻¹ = tau * (rho z)⁻¹ := by rw [hz, mul_inv_rev, tau_inv]
    rw [hζ', hz]
    have h1 : rho z * tau * specialRho (A, B) * (tau * (rho z)⁻¹) =
        rho (z * transposePair (specialPairs (A, B)) * z⁻¹) := by
      rw [map_mul, map_mul, map_inv, ← tau_rho_tau]
      change rho z * tau * rho (specialPairs (A, B)) * (tau * (rho z)⁻¹) =
        rho z * (tau * rho (specialPairs (A, B)) * tau) * (rho z)⁻¹
      group
    rw [h1]
    change rho _ = rho (specialPairs (A', B'))
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · exact hA'.symm
    · exact hB'.symm

theorem commute_conj_inverseTranspose (z : Matrix.GeneralLinearGroup (Fin 2) K)
    {g h : Matrix.GeneralLinearGroup (Fin 2) K} (hc : Commute g h) :
    Commute (z * inverseTranspose g * z⁻¹) (z * inverseTranspose h * z⁻¹) := by
  have h1 : Commute (inverseTranspose g) (inverseTranspose h) := by
    change inverseTranspose g * inverseTranspose h = inverseTranspose h * inverseTranspose g
    rw [← inverseTranspose_mul, ← inverseTranspose_mul, hc.eq]
  have := h1.map (MulAut.conj z).toMonoidHom
  simpa [MulAut.conj_apply] using this

theorem commute_iff_of_swap_fixed [Finite K] [CharP K 2] {ζ : DeterminantIsometries K}
    (hζ : ζ ∉ specialImage K) {a₁ b₁ a₂ b₂ : SL(2, K)}
    (h₁ : ζ * specialRho (a₁, b₁) * ζ⁻¹ = specialRho (a₁, b₁))
    (h₂ : ζ * specialRho (a₂, b₂) * ζ⁻¹ = specialRho (a₂, b₂)) :
    Commute a₁ a₂ ↔ Commute b₁ b₂ := by
  obtain ⟨z₁, z₂, hz⟩ := exists_swap hζ
  have key : ∀ a b : SL(2, K), ζ * specialRho (a, b) * ζ⁻¹ = specialRho (a, b) →
      Matrix.SpecialLinearGroup.toGL a =
        z₁ * inverseTranspose (Matrix.SpecialLinearGroup.toGL b) * z₁⁻¹ ∧
      Matrix.SpecialLinearGroup.toGL b =
        z₂ * inverseTranspose (Matrix.SpecialLinearGroup.toGL a) * z₂⁻¹ := by
    intro a b h
    obtain ⟨A', B', hA', hB', hconj⟩ := hz a b
    have hab : (A', B') = (a, b) := specialRho_injective (hconj.symm.trans h)
    exact ⟨by rw [← hA', (Prod.mk.inj hab).1], by rw [← hB', (Prod.mk.inj hab).2]⟩
  obtain ⟨ha₁, hb₁⟩ := key a₁ b₁ h₁
  obtain ⟨ha₂, hb₂⟩ := key a₂ b₂ h₂
  constructor
  · intro hc
    have h1 : Commute (Matrix.SpecialLinearGroup.toGL a₁) (Matrix.SpecialLinearGroup.toGL a₂) :=
      hc.map Matrix.SpecialLinearGroup.toGL
    have h2 := commute_conj_inverseTranspose z₂ h1
    rw [← hb₁, ← hb₂] at h2
    exact Matrix.SpecialLinearGroup.toGL_injective (by rw [map_mul, map_mul]; exact h2.eq)
  · intro hc
    have h1 : Commute (Matrix.SpecialLinearGroup.toGL b₁) (Matrix.SpecialLinearGroup.toGL b₂) :=
      hc.map Matrix.SpecialLinearGroup.toGL
    have h2 := commute_conj_inverseTranspose z₁ h1
    rw [← ha₁, ← ha₂] at h2
    exact Matrix.SpecialLinearGroup.toGL_injective (by rw [map_mul, map_mul]; exact h2.eq)

end Model

section Linear

variable {K : Type} [Field K]

theorem exists_sl_add_eq_smul (c : K) :
    ∃ A B : SL(2, K), (A : Matrix (Fin 2) (Fin 2) K) + (B : Matrix (Fin 2) (Fin 2) K) =
      c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  refine ⟨⟨!![0, -1; 1, c], by simp [Matrix.det_fin_two]⟩, ⟨!![c, 1; -1, 0], by
    simp [Matrix.det_fin_two]⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem map_smul_of_commute_left {F : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K}
    (hadd : ∀ X Y, F (X + Y) = F X + F Y)
    (hF : ∀ (A : SL(2, K)) X, F ((A : Matrix (Fin 2) (Fin 2) K) * X) =
      (A : Matrix (Fin 2) (Fin 2) K) * F X) (c : K) (X : Matrix (Fin 2) (Fin 2) K) :
    F (c • X) = c • F X := by
  obtain ⟨A, B, h⟩ := exists_sl_add_eq_smul c
  have h1 : c • X = (A : Matrix (Fin 2) (Fin 2) K) * X + (B : Matrix (Fin 2) (Fin 2) K) * X := by
    rw [← add_mul, h, smul_mul_assoc, one_mul]
  rw [h1, hadd, hF, hF, ← add_mul, h, smul_mul_assoc, one_mul]

theorem map_smul_of_commute_right {F : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K}
    (hadd : ∀ X Y, F (X + Y) = F X + F Y)
    (hF : ∀ (B : SL(2, K)) X, F (X * (B : Matrix (Fin 2) (Fin 2) K)) =
      F X * (B : Matrix (Fin 2) (Fin 2) K)) (c : K) (X : Matrix (Fin 2) (Fin 2) K) :
    F (c • X) = c • F X := by
  obtain ⟨A, B, h⟩ := exists_sl_add_eq_smul c
  have h1 : c • X = X * (A : Matrix (Fin 2) (Fin 2) K) + X * (B : Matrix (Fin 2) (Fin 2) K) := by
    rw [← mul_add, h, mul_smul_comm, mul_one]
  rw [h1, hadd, hF, hF, ← mul_add, h, mul_smul_comm, mul_one]

theorem eq_of_semilinear_of_linear {σ : K →+* K}
    {F : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K}
    (hadd : ∀ X Y, F (X + Y) = F X + F Y) (hinj : Function.Injective F)
    (hs : ∀ (c : K) X, F (c • X) = σ c • F X) (hlin : ∀ (c : K) X, F (c • X) = c • F X) (c : K) :
    σ c = c := by
  have h0 : F 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    simpa using h
  have hne : F 1 ≠ 0 := fun h => one_ne_zero (hinj (h.trans h0.symm))
  have h1 : (σ c - c) • F 1 = 0 := by
    rw [sub_smul, ← hs, ← hlin, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hne)

theorem eq_of_semilinear_of_commute_left {σ : K →+* K}
    {F : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K}
    (hadd : ∀ X Y, F (X + Y) = F X + F Y) (hinj : Function.Injective F)
    (hs : ∀ (c : K) X, F (c • X) = σ c • F X)
    (hF : ∀ (A : SL(2, K)) X, F ((A : Matrix (Fin 2) (Fin 2) K) * X) =
      (A : Matrix (Fin 2) (Fin 2) K) * F X) (c : K) : σ c = c :=
  eq_of_semilinear_of_linear hadd hinj hs (map_smul_of_commute_left hadd hF) c

theorem eq_of_semilinear_of_commute_right {σ : K →+* K}
    {F : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K}
    (hadd : ∀ X Y, F (X + Y) = F X + F Y) (hinj : Function.Injective F)
    (hs : ∀ (c : K) X, F (c • X) = σ c • F X)
    (hF : ∀ (B : SL(2, K)) X, F (X * (B : Matrix (Fin 2) (Fin 2) K)) =
      F X * (B : Matrix (Fin 2) (Fin 2) K)) (c : K) : σ c = c :=
  eq_of_semilinear_of_linear hadd hinj hs (map_smul_of_commute_right hadd hF) c

end Linear

end CFSG.RankThree.PartOne
