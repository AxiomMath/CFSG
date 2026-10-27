module

public import CFSG.Quasithin.SteinbergCBTwistedField
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.Basify

public section

namespace CFSG.Quasithin.SteinbergCB

open Matrix
open scoped TensorProduct

variable {F : Type*} [Field F] (σ : F →+* F)

@[expose] def twistedForm : Submodule (frobFixed σ) (Matrix (Fin 2) (Fin 2) F) where
  carrier := {X | Xᵀ = X.map σ}
  add_mem' {X Y} hX hY := by
    have hX' : Xᵀ = X.map σ := hX
    have hY' : Yᵀ = Y.map σ := hY
    change (X + Y)ᵀ = (X + Y).map σ
    rw [transpose_add, hX', hY']
    ext i j
    simp
  zero_mem' := by
    change (0 : Matrix (Fin 2) (Fin 2) F)ᵀ = (0 : Matrix (Fin 2) (Fin 2) F).map σ
    ext i j
    simp
  smul_mem' c {X} hX := by
    have hX' : Xᵀ = X.map σ := hX
    change (c • X)ᵀ = (c • X).map σ
    rw [transpose_smul, hX']
    ext i j
    simp [Subfield.smul_def, frobFixed_apply]

variable {σ}

theorem mem_twistedForm {X : Matrix (Fin 2) (Fin 2) F} : X ∈ twistedForm σ ↔ Xᵀ = X.map σ :=
  Iff.rfl

theorem twistedForm_entry {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ twistedForm σ) (i j : Fin 2) :
    σ (X i j) = X j i :=
  (congrFun (congrFun hX i) j).symm

theorem twistedForm_diag_mem {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ twistedForm σ) (i : Fin 2) :
    X i i ∈ frobFixed σ :=
  mem_frobFixed.2 (twistedForm_entry hX i i)

variable (σ)

@[expose] def twistLin (g : Matrix (Fin 2) (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F →ₗ[F] Matrix (Fin 2) (Fin 2) F where
  toFun X := g * X * (g.map σ)ᵀ
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem twistLin_apply (g X : Matrix (Fin 2) (Fin 2) F) : twistLin σ g X = g * X * (g.map σ)ᵀ :=
  rfl

variable {σ}

theorem twist_mem (hinv : ∀ x, σ (σ x) = x) (g : Matrix (Fin 2) (Fin 2) F)
    {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ twistedForm σ) :
    g * X * (g.map σ)ᵀ ∈ twistedForm σ := by
  have hX' : Xᵀ = X.map σ := hX
  have hgg : (g.map σ).map σ = g := by
    ext i j
    simp [hinv]
  change (g * X * (g.map σ)ᵀ)ᵀ = (g * X * (g.map σ)ᵀ).map σ
  rw [transpose_mul, transpose_mul, transpose_transpose, Matrix.map_mul, Matrix.map_mul,
    transpose_map, hgg, hX', Matrix.mul_assoc]

@[expose] def twistEnd (hinv : ∀ x, σ (σ x) = x) (g : Matrix (Fin 2) (Fin 2) F) :
    Module.End (frobFixed σ) (twistedForm σ) :=
  ((twistLin σ g).restrictScalars (frobFixed σ)).restrict (fun _ hX => twist_mem hinv g hX)

theorem twistEnd_apply (hinv : ∀ x, σ (σ x) = x) (g : Matrix (Fin 2) (Fin 2) F)
    (X : twistedForm σ) :
    ((twistEnd hinv g X : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) =
      g * (X : Matrix (Fin 2) (Fin 2) F) * (g.map σ)ᵀ :=
  rfl

theorem twistEnd_one (hinv : ∀ x, σ (σ x) = x) : twistEnd hinv 1 = 1 := by
  apply LinearMap.ext
  intro X
  apply Subtype.ext
  rw [twistEnd_apply, ← RingHom.mapMatrix_apply, map_one, transpose_one, Matrix.one_mul,
    Matrix.mul_one]
  rfl

theorem twistEnd_mul (hinv : ∀ x, σ (σ x) = x) (g h : Matrix (Fin 2) (Fin 2) F) :
    twistEnd hinv (g * h) = twistEnd hinv g * twistEnd hinv h := by
  apply LinearMap.ext
  intro X
  apply Subtype.ext
  rw [Module.End.mul_apply, twistEnd_apply, twistEnd_apply, twistEnd_apply, Matrix.map_mul,
    transpose_mul]
  simp only [Matrix.mul_assoc]

@[expose] def twistRep (hinv : ∀ x, σ (σ x) = x) :
    Matrix.SpecialLinearGroup (Fin 2) F →* (twistedForm σ ≃ₗ[frobFixed σ] twistedForm σ) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).toMonoidHom.comp
    (MonoidHom.toHomUnits
      { toFun := fun g => twistEnd hinv (g : Matrix (Fin 2) (Fin 2) F)
        map_one' := twistEnd_one hinv
        map_mul' := fun _ _ => twistEnd_mul hinv _ _ })

theorem twistRep_apply (hinv : ∀ x, σ (σ x) = x) (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (X : twistedForm σ) :
    ((twistRep hinv g X : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) =
      (g : Matrix (Fin 2) (Fin 2) F) * X * ((g : Matrix (Fin 2) (Fin 2) F).map σ)ᵀ :=
  rfl

@[expose] def twMk (hinv : ∀ x, σ (σ x) = x) (a : frobFixed σ) (b : F) (d : frobFixed σ) :
    twistedForm σ :=
  ⟨!![(a : F), b; σ b, (d : F)], by
    rw [mem_twistedForm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hinv, frobFixed_apply]⟩

theorem twMk_coe (hinv : ∀ x, σ (σ x) = x) (a : frobFixed σ) (b : F) (d : frobFixed σ) :
    ((twMk hinv a b d : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) = !![(a : F), b; σ b, (d : F)] :=
  rfl

theorem twistedForm_eq (X : twistedForm σ) :
    (X : Matrix (Fin 2) (Fin 2) F) =
      !![(X : Matrix (Fin 2) (Fin 2) F) 0 0, (X : Matrix (Fin 2) (Fin 2) F) 0 1;
        σ ((X : Matrix (Fin 2) (Fin 2) F) 0 1), (X : Matrix (Fin 2) (Fin 2) F) 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twistedForm_entry X.2 0 1]

@[expose] def twistCoord (hinv : ∀ x, σ (σ x) = x) :
    twistedForm σ ≃ₗ[frobFixed σ] frobFixed σ × F × frobFixed σ where
  toFun X := (⟨(X : Matrix (Fin 2) (Fin 2) F) 0 0, twistedForm_diag_mem X.2 0⟩,
    (X : Matrix (Fin 2) (Fin 2) F) 0 1, ⟨(X : Matrix (Fin 2) (Fin 2) F) 1 1,
      twistedForm_diag_mem X.2 1⟩)
  map_add' X Y := by
    ext <;> simp
  map_smul' c X := by
    ext <;> simp [Subfield.smul_def]
  invFun p := twMk hinv p.1 p.2.1 p.2.2
  left_inv X := by
    apply Subtype.ext
    rw [twMk_coe]
    exact (twistedForm_eq X).symm
  right_inv p := by
    ext <;> simp [twMk_coe]

theorem finrank_twistedForm [Finite F] (hinv : ∀ x, σ (σ x) = x) {ω : F} (hω : σ ω ≠ ω) :
    Module.finrank (frobFixed σ) (twistedForm σ) = 4 := by
  have : Module.Finite (frobFixed σ) F := Module.Finite.of_finite
  rw [(twistCoord hinv).finrank_eq, Module.finrank_prod, Module.finrank_prod,
    Module.finrank_self, finrank_frobFixed_eq_two hinv hω]

theorem liftBaseChange_twistedForm_surjective (hinv : ∀ x, σ (σ x) = x) {ω : F}
    (hω : σ ω ≠ ω) :
    Function.Surjective ((twistedForm σ).subtype.liftBaseChange F) := by
  intro M
  have hne : ω - σ ω ≠ 0 := sub_ne_zero.2 (Ne.symm hω)
  set β := (M 0 1 - M 1 0) / (ω - σ ω) with hβ
  have hβω : β * (ω - σ ω) = M 0 1 - M 1 0 := div_mul_cancel₀ _ hne
  refine ⟨M 0 0 ⊗ₜ twMk hinv 1 0 0 + M 1 1 ⊗ₜ twMk hinv 0 0 1 +
    (M 0 1 - β * ω) ⊗ₜ twMk hinv 0 1 0 + β ⊗ₜ twMk hinv 0 ω 0, ?_⟩
  simp only [map_add, LinearMap.liftBaseChange_tmul, Submodule.subtype_apply, twMk_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  linear_combination -hβω

theorem finrank_matrix_two : Module.finrank F (Matrix (Fin 2) (Fin 2) F) = 4 := by
  rw [Module.finrank_matrix, Module.finrank_self, Fintype.card_fin]

theorem liftBaseChange_twistedForm_bijective [Finite F] (hinv : ∀ x, σ (σ x) = x) {ω : F}
    (hω : σ ω ≠ ω) :
    Function.Bijective ((twistedForm σ).subtype.liftBaseChange F) := by
  have hsurj := liftBaseChange_twistedForm_surjective hinv hω
  refine ⟨?_, hsurj⟩
  have : Module.Finite (frobFixed σ) (twistedForm σ) := Module.Finite.of_finite
  have hrank : Module.finrank F (F ⊗[frobFixed σ] twistedForm σ) =
      Module.finrank F (Matrix (Fin 2) (Fin 2) F) := by
    rw [Module.finrank_baseChange, finrank_twistedForm hinv hω, finrank_matrix_two]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).2 hsurj

theorem liftBaseChange_twistRep (hinv : ∀ x, σ (σ x) = x) (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (t : F ⊗[frobFixed σ] twistedForm σ) :
    (twistedForm σ).subtype.liftBaseChange F
        (LinearMap.baseChange F (twistRep hinv g).toLinearMap t) =
      (g : Matrix (Fin 2) (Fin 2) F) * (twistedForm σ).subtype.liftBaseChange F t *
        ((g : Matrix (Fin 2) (Fin 2) F).map σ)ᵀ := by
  induction t using TensorProduct.inductionOn with
  | tmul c X =>
    rw [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul,
      Submodule.subtype_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, twistRep_apply,
      Matrix.mul_smul, Matrix.smul_mul]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add, Matrix.mul_add, Matrix.add_mul]

theorem det_mem_frobFixed {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ twistedForm σ) :
    X.det ∈ frobFixed σ := by
  rw [mem_frobFixed, RingHom.map_det, RingHom.mapMatrix_apply, ← mem_twistedForm.1 hX,
    det_transpose]

variable (σ) in
@[expose] def twistedPolar : LinearMap.BilinForm (frobFixed σ) (twistedForm σ) :=
  LinearMap.mk₂ (frobFixed σ)
    (fun X Y => ⟨((X + Y : twistedForm σ) : Matrix (Fin 2) (Fin 2) F).det -
      (X : Matrix (Fin 2) (Fin 2) F).det - (Y : Matrix (Fin 2) (Fin 2) F).det,
      sub_mem (sub_mem (det_mem_frobFixed (X + Y).2) (det_mem_frobFixed X.2))
        (det_mem_frobFixed Y.2)⟩)
    (fun X₁ X₂ Y => by
      apply Subtype.ext
      simp [det_fin_two]
      ring)
    (fun c X Y => by
      apply Subtype.ext
      simp [det_fin_two, Subfield.smul_def]
      ring)
    (fun X Y₁ Y₂ => by
      apply Subtype.ext
      simp [det_fin_two]
      ring)
    (fun c X Y => by
      apply Subtype.ext
      simp [det_fin_two, Subfield.smul_def]
      ring)

variable (σ) in
@[expose] def twistedDet : QuadraticForm (frobFixed σ) (twistedForm σ) where
  toFun X := ⟨(X : Matrix (Fin 2) (Fin 2) F).det, det_mem_frobFixed X.2⟩
  toFun_smul c X := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, det_fin_two, Matrix.smul_apply, Subfield.smul_def,
      smul_eq_mul, Subfield.coe_mul]
    ring
  exists_companion' := ⟨twistedPolar σ, fun X Y => by
    apply Subtype.ext
    simp [twistedPolar]⟩

theorem twistedDet_apply (X : twistedForm σ) :
    ((twistedDet σ X : frobFixed σ) : F) = (X : Matrix (Fin 2) (Fin 2) F).det :=
  rfl

theorem twistedDet_polar (X Y : twistedForm σ) :
    ((QuadraticMap.polar (twistedDet σ) X Y : frobFixed σ) : F) =
      (X : Matrix (Fin 2) (Fin 2) F) 0 0 * (Y : Matrix (Fin 2) (Fin 2) F) 1 1 +
        (Y : Matrix (Fin 2) (Fin 2) F) 0 0 * (X : Matrix (Fin 2) (Fin 2) F) 1 1 -
        (X : Matrix (Fin 2) (Fin 2) F) 0 1 * (Y : Matrix (Fin 2) (Fin 2) F) 1 0 -
        (Y : Matrix (Fin 2) (Fin 2) F) 0 1 * (X : Matrix (Fin 2) (Fin 2) F) 1 0 := by
  simp only [QuadraticMap.polar, AddSubgroupClass.coe_sub, twistedDet_apply, Submodule.coe_add,
    det_fin_two, Matrix.add_apply]
  ring

theorem twistedDet_twistRep (hinv : ∀ x, σ (σ x) = x) (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (X : twistedForm σ) : twistedDet σ (twistRep hinv g X) = twistedDet σ X := by
  apply Subtype.ext
  rw [twistedDet_apply, twistedDet_apply, twistRep_apply, det_mul, det_mul, det_transpose,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe, map_one,
    one_mul, mul_one]

theorem twistedDet_polar_twMk (hinv : ∀ x, σ (σ x) = x) (X : twistedForm σ) (a : frobFixed σ)
    (b : F) (d : frobFixed σ) :
    ((QuadraticMap.polar (twistedDet σ) X (twMk hinv a b d) : frobFixed σ) : F) =
      (X : Matrix (Fin 2) (Fin 2) F) 0 0 * d + a * (X : Matrix (Fin 2) (Fin 2) F) 1 1 -
        (X : Matrix (Fin 2) (Fin 2) F) 0 1 * σ b - b * σ ((X : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  rw [twistedDet_polar, twMk_coe, ← twistedForm_entry X.2 0 1]
  simp

theorem twistedDet_polar_nondegenerate (h2 : (2 : F) = 0) (hinv : ∀ x, σ (σ x) = x) {ω : F}
    (hω : σ ω ≠ ω) (X : twistedForm σ)
    (hX : ∀ Y, QuadraticMap.polar (twistedDet σ) X Y = 0) : X = 0 := by
  have hpol : ∀ (a : frobFixed σ) (b : F) (d : frobFixed σ),
      (X : Matrix (Fin 2) (Fin 2) F) 0 0 * (d : F) +
      (a : F) * (X : Matrix (Fin 2) (Fin 2) F) 1 1 -
        (X : Matrix (Fin 2) (Fin 2) F) 0 1 * σ b -
          b * σ ((X : Matrix (Fin 2) (Fin 2) F) 0 1) = 0 := fun a b d => by
    rw [← twistedDet_polar_twMk hinv, hX]
    rfl
  have h11 := hpol 1 0 0
  have h00 := hpol 0 0 1
  simp only [ZeroMemClass.coe_zero, OneMemClass.coe_one, map_zero, mul_zero, zero_mul, one_mul,
    mul_one, sub_zero, zero_add, add_zero] at h11 h00
  have h01 : (X : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    by_contra hb
    have hσb : σ ((X : Matrix (Fin 2) (Fin 2) F) 0 1) ≠ 0 := (map_ne_zero σ).2 hb
    have h := hpol 0 (σ (ω / (X : Matrix (Fin 2) (Fin 2) F) 0 1)) 0
    rw [hinv, map_div₀, mul_div_cancel₀ _ hb, div_mul_cancel₀ _ hσb] at h
    simp only [ZeroMemClass.coe_zero, mul_zero, zero_mul, add_zero, zero_sub] at h
    exact hω (by linear_combination -h - ω * h2)
  apply Subtype.ext
  rw [twistedForm_eq X, h00, h01, h11]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

variable (σ) in
@[expose] def twistDiag : twistedForm σ →ₗ[frobFixed σ] frobFixed σ × frobFixed σ where
  toFun X := (⟨(X : Matrix (Fin 2) (Fin 2) F) 0 0, twistedForm_diag_mem X.2 0⟩,
    ⟨(X : Matrix (Fin 2) (Fin 2) F) 1 1, twistedForm_diag_mem X.2 1⟩)
  map_add' X Y := by
    ext <;> simp
  map_smul' c X := by
    ext <;> simp [Subfield.smul_def]

theorem mem_ker_twistDiag {X : twistedForm σ} :
    X ∈ LinearMap.ker (twistDiag σ) ↔
      (X : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 ∧ (X : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
  rw [LinearMap.mem_ker, Prod.ext_iff]
  simp [twistDiag, Subtype.ext_iff]

theorem eq_zero_of_mem_ker_twistDiag {X : twistedForm σ} (hX : X ∈ LinearMap.ker (twistDiag σ))
    (hQ : twistedDet σ X = 0) : X = 0 := by
  obtain ⟨h00, h11⟩ := mem_ker_twistDiag.1 hX
  have hQ' : (X : Matrix (Fin 2) (Fin 2) F).det = 0 := by
    rw [← twistedDet_apply, hQ]
    rfl
  rw [det_fin_two, h00, h11, ← twistedForm_entry X.2 0 1] at hQ'
  have h01 : (X : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 :=
    frob_norm_eq_zero (by linear_combination -hQ')
  apply Subtype.ext
  rw [twistedForm_eq X, h00, h01, h11]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem isCompl_span_ker_twistDiag (hinv : ∀ x, σ (σ x) = x) :
    IsCompl (Submodule.span (frobFixed σ) {twMk hinv 1 0 0, twMk hinv 0 0 1})
      (LinearMap.ker (twistDiag σ)) := by
  rw [isCompl_iff, Submodule.disjoint_def, codisjoint_iff]
  refine ⟨fun X hX hA => ?_, ?_⟩
  · obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hX
    obtain ⟨h00, h11⟩ := mem_ker_twistDiag.1 hA
    simp [twMk_coe, Subfield.smul_def] at h00 h11
    rw [h00, h11, zero_smul, zero_smul, add_zero]
  · rw [eq_top_iff]
    intro X _
    rw [Submodule.mem_sup]
    set a : frobFixed σ := ⟨(X : Matrix (Fin 2) (Fin 2) F) 0 0, twistedForm_diag_mem X.2 0⟩
    set d : frobFixed σ := ⟨(X : Matrix (Fin 2) (Fin 2) F) 1 1, twistedForm_diag_mem X.2 1⟩
    refine ⟨a • twMk hinv 1 0 0 + d • twMk hinv 0 0 1,
      Submodule.mem_span_pair.2 ⟨a, d, rfl⟩, X - (a • twMk hinv 1 0 0 + d • twMk hinv 0 0 1),
      ?_, add_sub_cancel _ _⟩
    rw [mem_ker_twistDiag]
    simp [twMk_coe, Subfield.smul_def, a, d]

theorem polar_twMk_of_mem_ker (hinv : ∀ x, σ (σ x) = x) {X : twistedForm σ}
    (hX : X ∈ LinearMap.ker (twistDiag σ)) :
    QuadraticMap.polar (twistedDet σ) (twMk hinv 1 0 0) X = 0 ∧
      QuadraticMap.polar (twistedDet σ) (twMk hinv 0 0 1) X = 0 := by
  obtain ⟨h00, h11⟩ := mem_ker_twistDiag.1 hX
  constructor <;>
  · rw [QuadraticMap.polar_comm]
    apply Subtype.ext
    rw [twistedDet_polar_twMk, h00, h11]
    simp

theorem finrank_ker_twistDiag [Finite F] (hinv : ∀ x, σ (σ x) = x) {ω : F} (hω : σ ω ≠ ω) :
    Module.finrank (frobFixed σ) (LinearMap.ker (twistDiag σ)) = 2 := by
  have : Module.Finite (frobFixed σ) (twistedForm σ) := Module.Finite.of_finite
  have hsurj : Function.Surjective (twistDiag σ) := fun p =>
    ⟨twMk hinv p.1 0 p.2, by ext <;> simp [twistDiag, twMk_coe]⟩
  have h := LinearMap.finrank_range_add_finrank_ker (twistDiag σ)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_prod, Module.finrank_self,
    finrank_twistedForm hinv hω] at h
  omega

theorem finrank_le_one_of_totally_singular [Finite F]
    (U : Submodule (frobFixed σ) (twistedForm σ)) (hU : ∀ u ∈ U, twistedDet σ u = 0) :
    Module.finrank (frobFixed σ) U ≤ 1 := by
  have : Module.Finite (frobFixed σ) (twistedForm σ) := Module.Finite.of_finite
  have hinj : Function.Injective ((twistDiag σ).comp U.subtype) := by
    intro u v huv
    have hmem : (u : twistedForm σ) - v ∈ LinearMap.ker (twistDiag σ) := by
      rw [LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.2 huv
    have h := eq_zero_of_mem_ker_twistDiag hmem (hU _ (U.sub_mem u.2 v.2))
    exact Subtype.ext (sub_eq_zero.1 h)
  have h2 : Module.finrank (frobFixed σ) (frobFixed σ × frobFixed σ) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  by_contra hlt
  push Not at hlt
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have heq : Module.finrank (frobFixed σ) U =
      Module.finrank (frobFixed σ) (frobFixed σ × frobFixed σ) := by
    omega
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := frobFixed σ)
    (V := U) (V₂ := frobFixed σ × frobFixed σ) heq (f := (twistDiag σ).comp U.subtype)).1 hinj
  have key : ∀ w : U, ((w : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 0 *
      ((w : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 →
        ((w : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := fun w hw => by
    have hQw : ((w : twistedForm σ) : Matrix (Fin 2) (Fin 2) F).det = 0 := by
      rw [← twistedDet_apply, hU _ w.2]
      rfl
    rw [det_fin_two, hw, ← twistedForm_entry (w : twistedForm σ).2 0 1] at hQw
    exact frob_norm_eq_zero (by linear_combination -hQw)
  obtain ⟨u, hu⟩ := hsurj (1, 0)
  obtain ⟨v, hv⟩ := hsurj (0, 1)
  have hu00 : ((u : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 :=
    congrArg (fun q => (q.1 : F)) hu
  have hu11 : ((u : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 :=
    congrArg (fun q => (q.2 : F)) hu
  have hv00 : ((v : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 :=
    congrArg (fun q => (q.1 : F)) hv
  have hv11 : ((v : twistedForm σ) : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 :=
    congrArg (fun q => (q.2 : F)) hv
  have hu01 := key u (by rw [hu11, mul_zero])
  have hv01 := key v (by rw [hv00, zero_mul])
  have hpol : QuadraticMap.polar (twistedDet σ) (u : twistedForm σ) v = 0 := by
    rw [QuadraticMap.polar, hU _ (U.add_mem u.2 v.2), hU _ u.2, hU _ v.2, sub_zero, sub_zero]
  have h := congrArg Subtype.val hpol
  rw [twistedDet_polar, ← twistedForm_entry (u : twistedForm σ).2 0 1,
    ← twistedForm_entry (v : twistedForm σ).2 0 1, hu00, hu11, hv00, hv11, hu01, hv01] at h
  simp at h

end CFSG.Quasithin.SteinbergCB
