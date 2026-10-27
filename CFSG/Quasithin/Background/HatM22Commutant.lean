module

public import CFSG.Quasithin.Background.SmithB45M22HatModel
public import CFSG.Quasithin.Background.HatM22CommutantData

public section

namespace CFSG.Quasithin.HatM22

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour
open scoped Matrix

@[expose] def hatM22CommComb (A₁ A₂ : Matrix (Fin 6) (Fin 6) FieldFour) :
    Matrix (Fin 6) (Fin 6) FieldFour :=
  (hatM22N1 * A₁ + A₁ * hatM22N1) + (hatM22N2 * A₂ + A₂ * hatM22N2)

theorem hatM22CommCert_ok :
    ∀ p ∈ hatM22CommCert,
      hatM22CommComb (untab p.2.2.1) (untab p.2.2.2) = (hatM22Tgt p.1 p.2.1)ᵀ := by
  decide +kernel

theorem hatM22CommCert_keys : ∀ a b : Fin 6, a ≠ b ∨ a ≠ 0 →
    (a, b) ∈ hatM22CommCert.map fun p => (p.1, p.2.1) := by
  decide +kernel

theorem hatM22CommCert_cover (a b : Fin 6) (h : a ≠ b ∨ a ≠ 0) :
    ∃ A₁ A₂, (a, b, A₁, A₂) ∈ hatM22CommCert := by
  obtain ⟨⟨a', b', A₁, A₂⟩, hP, he⟩ := List.mem_map.1 (hatM22CommCert_keys a b h)
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨A₁, A₂, hP⟩

theorem trace_add_mul_comm (A N Y : Matrix (Fin 6) (Fin 6) FieldFour) (h : Y * N = N * Y) :
    ((N * A + A * N) * Y).trace = 0 := by
  rw [Matrix.add_mul, Matrix.trace_add]
  have e : (N * A * Y).trace = (A * N * Y).trace := by
    calc (N * A * Y).trace = (Y * (N * A)).trace := Matrix.trace_mul_comm _ _
      _ = (Y * N * A).trace := by rw [Matrix.mul_assoc]
      _ = (N * Y * A).trace := by rw [h]
      _ = (A * (N * Y)).trace := (Matrix.trace_mul_comm _ _).symm
      _ = (A * N * Y).trace := by rw [Matrix.mul_assoc]
  rw [e, CharTwo.add_self_eq_zero]

theorem trace_commComb_mul (A₁ A₂ Y : Matrix (Fin 6) (Fin 6) FieldFour)
    (h₁ : Y * hatM22N1 = hatM22N1 * Y) (h₂ : Y * hatM22N2 = hatM22N2 * Y) :
    (hatM22CommComb A₁ A₂ * Y).trace = 0 := by
  have hA₁ := trace_add_mul_comm A₁ hatM22N1 Y h₁
  have hA₂ := trace_add_mul_comm A₂ hatM22N2 Y h₂
  rw [hatM22CommComb, Matrix.add_mul, Matrix.trace_add, hA₁, hA₂]
  simp

theorem eq_smul_one_of_trace_tgt (Y : Matrix (Fin 6) (Fin 6) FieldFour)
    (h : ∀ a b : Fin 6, a ≠ b ∨ a ≠ 0 → ((hatM22Tgt a b)ᵀ * Y).trace = 0) :
    Y = Y 0 0 • 1 := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    rw [ite_eq_left rfl, mul_one]
    by_cases ha : a = 0
    · rw [ha]
    · have h' := h a a (Or.inr ha)
      rw [hatM22Tgt, ite_eq_left rfl, Matrix.transpose_add, Matrix.add_mul, Matrix.trace_add,
        trace_single_transpose_mul, trace_single_transpose_mul] at h'
      exact (CharTwo.add_eq_zero (R := FieldFour)).1 h'
  · have h' := h a b (Or.inl hab)
    rw [hatM22Tgt, ite_eq_right hab, trace_single_transpose_mul] at h'
    rw [ite_eq_right hab, mul_zero, h']

theorem eq_smul_one_of_commute_hatM22 (Y : Matrix (Fin 6) (Fin 6) FieldFour)
    (h1 : Y * hatM22N1 = hatM22N1 * Y) (h2 : Y * hatM22N2 = hatM22N2 * Y) :
    Y = Y 0 0 • 1 := by
  apply eq_smul_one_of_trace_tgt
  intro a b hab
  obtain ⟨A₁, A₂, hP⟩ := hatM22CommCert_cover a b hab
  have hok := hatM22CommCert_ok (a, b, A₁, A₂) hP
  rw [← hok]
  exact trace_commComb_mul (untab A₁) (untab A₂) Y h1 h2

theorem map_smul_of_commute_hatM22Z (φ : (Fin 6 → FieldFour) →+ (Fin 6 → FieldFour))
    (hφ : ∀ γ ∈ hatM22Γ₀, ∀ v : Fin 6 → FieldFour,
      φ (((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
        Matrix (Fin 6) (Fin 6) FieldFour).mulVec v) =
        ((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
          Matrix (Fin 6) (Fin 6) FieldFour).mulVec (φ v))
    (c : FieldFour) (v : Fin 6 → FieldFour) : φ (c • v) = c • φ v := by
  have hω : ∀ w : Fin 6 → FieldFour, φ (ω • w) = ω • φ w := by
    intro w
    have h := hφ (hatM22Z : Matrix.GeneralLinearGroup (Fin 6) FieldFour) hatM22Z.2 w
    simp only [hatM22Z_val, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    exact h
  have hω₂ : φ (ω₂ • v) = ω₂ • φ v := by
    have h := hω (ω • v)
    rw [smul_smul, ← pow_two, ω_sq, hω v, smul_smul, ← pow_two, ω_sq] at h
    exact h
  have hc : ∀ c : FieldFour, c = 0 ∨ c = 1 ∨ c = ω ∨ c = ω₂ := by decide
  rcases hc c with h0 | h1 | hω' | hω₂'
  · rw [h0, zero_smul, map_zero, zero_smul]
  · rw [h1, one_smul, one_smul]
  · rw [hω']; exact hω v
  · rw [hω₂']; exact hω₂

@[expose] noncomputable def hatM22EndLin (φ : (Fin 6 → FieldFour) →+ (Fin 6 → FieldFour))
    (hlin : ∀ c : FieldFour, ∀ v : Fin 6 → FieldFour, φ (c • v) = c • φ v) :
    (Fin 6 → FieldFour) →ₗ[FieldFour] (Fin 6 → FieldFour) where
  toFun := φ
  map_add' := φ.map_add
  map_smul' := hlin

@[expose] noncomputable def hatM22PhiMatrix (φ : (Fin 6 → FieldFour) →+ (Fin 6 → FieldFour))
    (hlin : ∀ c : FieldFour, ∀ v : Fin 6 → FieldFour, φ (c • v) = c • φ v) :
    Matrix (Fin 6) (Fin 6) FieldFour :=
  LinearMap.toMatrix' (hatM22EndLin φ hlin)

theorem hatM22PhiMatrix_mulVec (φ : (Fin 6 → FieldFour) →+ (Fin 6 → FieldFour))
    (hlin : ∀ c : FieldFour, ∀ v : Fin 6 → FieldFour, φ (c • v) = c • φ v)
    (v : Fin 6 → FieldFour) : (hatM22PhiMatrix φ hlin).mulVec v = φ v := by
  rw [hatM22PhiMatrix, LinearMap.toMatrix'_mulVec]
  rfl

theorem hatM22PhiMatrix_commute_N1 (φ : (Fin 6 → FieldFour) →+ (Fin 6 → FieldFour))
    (hlin : ∀ c : FieldFour, ∀ v : Fin 6 → FieldFour, φ (c • v) = c • φ v)
    (hφ : ∀ γ ∈ hatM22Γ₀, ∀ v : Fin 6 → FieldFour,
      φ (((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
        Matrix (Fin 6) (Fin 6) FieldFour).mulVec v) =
        ((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
          Matrix (Fin 6) (Fin 6) FieldFour).mulVec (φ v)) :
    hatM22PhiMatrix φ hlin * hatM22N1 = hatM22N1 * hatM22PhiMatrix φ hlin := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  simp only [LinearMap.comp_apply, Matrix.toLin'_apply]
  simp only [hatM22PhiMatrix_mulVec]
  exact hφ hatM22G1 hatM22G1_mem v

theorem hatM22PhiMatrix_commute_N2 (φ : (Fin 6 → FieldFour) →+ (Fin 6 → FieldFour))
    (hlin : ∀ c : FieldFour, ∀ v : Fin 6 → FieldFour, φ (c • v) = c • φ v)
    (hφ : ∀ γ ∈ hatM22Γ₀, ∀ v : Fin 6 → FieldFour,
      φ (((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
        Matrix (Fin 6) (Fin 6) FieldFour).mulVec v) =
        ((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
          Matrix (Fin 6) (Fin 6) FieldFour).mulVec (φ v)) :
    hatM22PhiMatrix φ hlin * hatM22N2 = hatM22N2 * hatM22PhiMatrix φ hlin := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  simp only [LinearMap.comp_apply, Matrix.toLin'_apply]
  simp only [hatM22PhiMatrix_mulVec]
  exact hφ hatM22G2 hatM22G2_mem v

theorem exists_eq_smul_of_commute_hatM22Γ₀ (φ : (Fin 6 → FieldFour) →+ (Fin 6 → FieldFour))
    (hφ : ∀ γ ∈ hatM22Γ₀, ∀ v : Fin 6 → FieldFour,
      φ (((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
        Matrix (Fin 6) (Fin 6) FieldFour).mulVec v) =
        ((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
          Matrix (Fin 6) (Fin 6) FieldFour).mulVec (φ v)) :
    ∃ c : FieldFour, ∀ v, φ v = c • v := by
  have hlin : ∀ c : FieldFour, ∀ v : Fin 6 → FieldFour, φ (c • v) = c • φ v :=
    map_smul_of_commute_hatM22Z φ hφ
  set Y : Matrix (Fin 6) (Fin 6) FieldFour := hatM22PhiMatrix φ hlin with hY
  have h1 : Y * hatM22N1 = hatM22N1 * Y := by
    rw [hY]
    exact hatM22PhiMatrix_commute_N1 φ hlin hφ
  have h2 : Y * hatM22N2 = hatM22N2 * Y := by
    rw [hY]
    exact hatM22PhiMatrix_commute_N2 φ hlin hφ
  refine ⟨Y 0 0, fun v => ?_⟩
  have hmv : Y.mulVec v = φ v := by
    rw [hY]
    exact hatM22PhiMatrix_mulVec φ hlin v
  rw [← hmv]
  conv_lhs => rw [eq_smul_one_of_commute_hatM22 Y h1 h2]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]

end CFSG.Quasithin.HatM22
