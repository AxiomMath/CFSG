module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.RankThree.GF2n.Smith81

open Matrix
open scoped MatrixGroups

abbrev Mat2 (K : Type*) [Field K] := Matrix (Fin 2) (Fin 2) K

namespace D2

variable {K : Type*} [Field K]

@[expose] def pairLin (g h : Mat2 K) : Mat2 K →ₗ[K] Mat2 K where
  toFun X := g * X * hᵀ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem pairLin_apply (g h X : Mat2 K) : pairLin g h X = g * X * hᵀ := rfl

theorem sl_mul_inv (g : SL(2, K)) :
    (g : Mat2 K) * ((g⁻¹ : SL(2, K)) : Mat2 K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem sl_inv_mul (g : SL(2, K)) :
    ((g⁻¹ : SL(2, K)) : Mat2 K) * (g : Mat2 K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

@[expose] def pairEquiv (g h : SL(2, K)) : Mat2 K ≃ₗ[K] Mat2 K :=
  { pairLin (g : Mat2 K) (h : Mat2 K) with
    invFun := fun X => ((g⁻¹ : SL(2, K)) : Mat2 K) * X * ((h⁻¹ : SL(2, K)) : Mat2 K)ᵀ
    left_inv := fun X => by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, pairLin_apply]
      calc ((g⁻¹ : SL(2, K)) : Mat2 K) * ((g : Mat2 K) * X * (h : Mat2 K)ᵀ) *
            ((h⁻¹ : SL(2, K)) : Mat2 K)ᵀ
          = (((g⁻¹ : SL(2, K)) : Mat2 K) * (g : Mat2 K)) * X *
            ((((h⁻¹ : SL(2, K)) : Mat2 K)) * (h : Mat2 K))ᵀ := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = X := by rw [sl_inv_mul, sl_inv_mul]; simp
    right_inv := fun X => by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, pairLin_apply]
      calc (g : Mat2 K) * (((g⁻¹ : SL(2, K)) : Mat2 K) * X * ((h⁻¹ : SL(2, K)) : Mat2 K)ᵀ) *
            (h : Mat2 K)ᵀ
          = ((g : Mat2 K) * ((g⁻¹ : SL(2, K)) : Mat2 K)) * X *
            ((h : Mat2 K) * ((h⁻¹ : SL(2, K)) : Mat2 K))ᵀ := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = X := by rw [sl_mul_inv, sl_mul_inv]; simp }

@[simp] theorem pairEquiv_apply (g h : SL(2, K)) (X : Mat2 K) :
    pairEquiv g h X = (g : Mat2 K) * X * (h : Mat2 K)ᵀ := rfl

theorem det_pairEquiv (g h : SL(2, K)) (X : Mat2 K) : (pairEquiv g h X).det = X.det := by
  rw [pairEquiv_apply, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.SpecialLinearGroup.det_coe, Matrix.SpecialLinearGroup.det_coe, one_mul, mul_one]

@[expose] def slMap (σ : K ≃+* K) : SL(2, K) →* SL(2, K) :=
  Matrix.SpecialLinearGroup.map (σ : K →+* K)

theorem coe_slMap (σ : K ≃+* K) (s : SL(2, K)) (i j : Fin 2) :
    ((slMap σ s : SL(2, K)) : Mat2 K) i j = σ ((s : Mat2 K) i j) := by
  simp [slMap, Matrix.SpecialLinearGroup.map_apply_coe]

@[expose] def twEquiv (σ : K ≃+* K) (s : SL(2, K)) : Mat2 K ≃ₗ[K] Mat2 K :=
  pairEquiv s (slMap σ s)

theorem twEquiv_apply (σ : K ≃+* K) (s : SL(2, K)) (X : Mat2 K) :
    twEquiv σ s X = (s : Mat2 K) * X * ((slMap σ s : SL(2, K)) : Mat2 K)ᵀ := rfl

theorem twEquiv_mul (σ : K ≃+* K) (s t : SL(2, K)) :
    twEquiv σ (s * t) = twEquiv σ s * twEquiv σ t := by
  refine LinearEquiv.ext fun X => ?_
  simp only [twEquiv_apply, LinearEquiv.mul_apply, map_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.transpose_mul, Matrix.mul_assoc]

theorem twEquiv_one (σ : K ≃+* K) : twEquiv σ 1 = 1 := by
  refine LinearEquiv.ext fun X => ?_
  simp [twEquiv_apply]

theorem det_twEquiv (σ : K ≃+* K) (s : SL(2, K)) (X : Mat2 K) :
    (twEquiv σ s X).det = X.det := det_pairEquiv _ _ X

theorem sl2_entries (g : SL(2, K)) :
    ∃ p q r s : K, (g : Mat2 K) = !![p, q; r, s] ∧ p * s - q * r = 1 := by
  refine ⟨(g : Mat2 K) 0 0, (g : Mat2 K) 0 1, (g : Mat2 K) 1 0, (g : Mat2 K) 1 1,
    Matrix.eta_fin_two _, ?_⟩
  have h := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at h
  exact h

@[expose] def uSL (a : K) : SL(2, K) := ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def lSL (a : K) : SL(2, K) := ⟨!![1, 0; a, 1], by simp [Matrix.det_fin_two]⟩

@[simp] theorem coe_uSL (a : K) : ((uSL a : SL(2, K)) : Mat2 K) = !![1, a; 0, 1] := rfl

@[simp] theorem coe_lSL (a : K) : ((lSL a : SL(2, K)) : Mat2 K) = !![1, 0; a, 1] := rfl

theorem sl2_fin_two_eq_iff {R : Type*} (a b c d a' b' c' d' : R) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) R) = !![a', b'; c', d'] ↔
      a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  constructor
  · intro h
    exact ⟨congrFun (congrFun h 0) 0, congrFun (congrFun h 0) 1,
      congrFun (congrFun h 1) 0, congrFun (congrFun h 1) 1⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

theorem sl2_eq_one_of_central [CharP K 2] {g : SL(2, K)} (h : ∀ A : SL(2, K), g * A = A * g) :
    g = 1 := by
  obtain ⟨p, q, r, s, hK, hdet⟩ := sl2_entries g
  have h1 : ((g * uSL 1 : SL(2, K)) : Mat2 K) = ((uSL 1 * g : SL(2, K)) : Mat2 K) := by
    rw [h (uSL 1)]
  have h2 : ((g * lSL 1 : SL(2, K)) : Mat2 K) = ((lSL 1 * g : SL(2, K)) : Mat2 K) := by
    rw [h (lSL 1)]
  simp only [Matrix.SpecialLinearGroup.coe_mul, hK, coe_uSL, coe_lSL] at h1 h2
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, sl2_fin_two_eq_iff] at h1 h2
  obtain ⟨a00, a01, -, -⟩ := h1
  obtain ⟨b00, -, -, -⟩ := h2
  have hr : r = 0 := by linear_combination -a00
  have hq : q = 0 := by linear_combination b00
  have hs : s = p := by linear_combination -a01
  have hpp : p * p = 1 := by linear_combination hdet - p * hs + q * hr
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hp2 : (p - 1) * (p - 1) = 0 := by linear_combination hpp + (1 - p) * h2K
  have hp : p = 1 := sub_eq_zero.mp (mul_self_eq_zero.mp hp2)
  have hs1 : s = 1 := hs.trans hp
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hK, hp, hq, hr, hs1]

theorem pair_unique [CharP K 2] {g g' h h' : SL(2, K)}
    (H : ∀ X : Mat2 K, (g : Mat2 K) * X * (h : Mat2 K)ᵀ = (g' : Mat2 K) * X * (h' : Mat2 K)ᵀ) :
    g = g' ∧ h = h' := by
  set a : SL(2, K) := g'⁻¹ * g with ha
  set c : SL(2, K) := h'⁻¹ * h with hc
  have key : ∀ X : Mat2 K, (a : Mat2 K) * X * (c : Mat2 K)ᵀ = X := by
    intro X
    have e1 : (a : Mat2 K) * X * (c : Mat2 K)ᵀ =
        ((g'⁻¹ : SL(2, K)) : Mat2 K) * ((g : Mat2 K) * X * (h : Mat2 K)ᵀ) *
          ((h'⁻¹ : SL(2, K)) : Mat2 K)ᵀ := by
      simp only [ha, hc, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e1, H X]
    calc ((g'⁻¹ : SL(2, K)) : Mat2 K) * ((g' : Mat2 K) * X * (h' : Mat2 K)ᵀ) *
          ((h'⁻¹ : SL(2, K)) : Mat2 K)ᵀ
        = (((g'⁻¹ : SL(2, K)) : Mat2 K) * (g' : Mat2 K)) * X *
          (((h'⁻¹ : SL(2, K)) : Mat2 K) * (h' : Mat2 K))ᵀ := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = X := by rw [sl_inv_mul, sl_inv_mul]; simp
  have hac : (a : Mat2 K) * (c : Mat2 K)ᵀ = 1 := by simpa using key 1
  have hcen : ∀ A : SL(2, K), a * A = A * a := by
    intro A
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have hk := key (A : Mat2 K)
    have e2 : (c : Mat2 K)ᵀ = ((a⁻¹ : SL(2, K)) : Mat2 K) := by
      have h3 : ((a⁻¹ : SL(2, K)) : Mat2 K) * ((a : Mat2 K) * (c : Mat2 K)ᵀ) =
          ((a⁻¹ : SL(2, K)) : Mat2 K) := by rw [hac, Matrix.mul_one]
      rw [← Matrix.mul_assoc, sl_inv_mul, Matrix.one_mul] at h3
      exact h3
    rw [e2] at hk
    have h4 : (a : Mat2 K) * (A : Mat2 K) = (A : Mat2 K) * (a : Mat2 K) := by
      have h5 := congrArg (fun Y => Y * (a : Mat2 K)) hk
      simp only [Matrix.mul_assoc, sl_inv_mul, Matrix.mul_one] at h5
      exact h5
    simpa [Matrix.SpecialLinearGroup.coe_mul] using congrFun (congrFun h4 i) j
  have ha1 : a = 1 := sl2_eq_one_of_central hcen
  have hcc : (c : Mat2 K)ᵀ = 1 := by
    have := key 1
    rw [ha1] at this
    simpa using this
  have hc1 : c = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have := congrFun (congrFun hcc j) i
    simpa [Matrix.transpose_apply, Matrix.one_apply, eq_comm] using this
  refine ⟨?_, ?_⟩
  · have := ha1
    rw [ha] at this
    exact (inv_mul_eq_one.mp this).symm
  · have := hc1
    rw [hc] at this
    exact (inv_mul_eq_one.mp this).symm

theorem slMap_symm_apply (σ : K ≃+* K) (t : SL(2, K)) : slMap σ (slMap σ.symm t) = t := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [coe_slMap, coe_slMap, σ.apply_symm_apply]

theorem normalizer_pair [CharP K 2] (σ : K ≃+* K) {g h : SL(2, K)}
    (hN : ∀ s : SL(2, K), ∃ s' : SL(2, K), ∀ X : Mat2 K,
      pairEquiv g h (twEquiv σ s X) = twEquiv σ s' (pairEquiv g h X)) : h = slMap σ g := by
  have key : ∀ s : SL(2, K), slMap σ (g * s * g⁻¹) = h * slMap σ s * h⁻¹ := by
    intro s
    obtain ⟨s', hs'⟩ := hN s
    have hpair : ∀ X : Mat2 K, ((g * s : SL(2, K)) : Mat2 K) * X *
        ((h * slMap σ s : SL(2, K)) : Mat2 K)ᵀ =
        ((s' * g : SL(2, K)) : Mat2 K) * X * ((slMap σ s' * h : SL(2, K)) : Mat2 K)ᵀ := by
      intro X
      have := hs' X
      simp only [pairEquiv_apply, twEquiv_apply] at this
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul,
        Matrix.mul_assoc] at this ⊢
      simpa [Matrix.mul_assoc] using this
    obtain ⟨e1, e2⟩ := pair_unique hpair
    have e3 : s' = g * s * g⁻¹ := by
      rw [e1]
      group
    rw [e3] at e2
    rw [eq_mul_inv_iff_mul_eq]
    simpa [map_mul, map_inv, mul_assoc] using e2.symm
  have hcen : ∀ t : SL(2, K), (h⁻¹ * slMap σ g) * t = t * (h⁻¹ * slMap σ g) := by
    intro t
    have k := key (slMap σ.symm t)
    simp only [map_mul, map_inv, slMap_symm_apply] at k
    have k2 : h⁻¹ * (slMap σ g * t * (slMap σ g)⁻¹) = t * h⁻¹ := by
      rw [k]
      group
    calc (h⁻¹ * slMap σ g) * t = h⁻¹ * (slMap σ g * t * (slMap σ g)⁻¹) * slMap σ g := by group
      _ = t * h⁻¹ * slMap σ g := by rw [k2]
      _ = t * (h⁻¹ * slMap σ g) := by group
  have h1 := sl2_eq_one_of_central hcen
  exact inv_mul_eq_one.mp h1

@[expose] def detIsom (K : Type*) [Field K] : Subgroup (Mat2 K ≃ₗ[K] Mat2 K) where
  carrier := {T | ∀ X, (T X).det = X.det}
  mul_mem' := fun {S T} hS hT X => by
    show (S (T X)).det = X.det
    rw [hS, hT]
  one_mem' := fun X => rfl
  inv_mem' := fun {T} hT X => by
    have h := hT (T.symm X)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

@[expose] def pairGroup (K : Type*) [Field K] : Subgroup (Mat2 K ≃ₗ[K] Mat2 K) where
  carrier := {T | ∃ g h : SL(2, K), ∀ X, T X = (g : Mat2 K) * X * (h : Mat2 K)ᵀ}
  mul_mem' := by
    rintro S T ⟨g₁, h₁, hS⟩ ⟨g₂, h₂, hT⟩
    refine ⟨g₁ * g₂, h₁ * h₂, fun X => ?_⟩
    show S (T X) = _
    rw [hT, hS]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  one_mem' := ⟨1, 1, fun X => by simp⟩
  inv_mem' := by
    rintro T ⟨g, h, hT⟩
    refine ⟨g⁻¹, h⁻¹, fun X => ?_⟩
    show T.symm X = _
    rw [LinearEquiv.symm_apply_eq, hT]
    calc X = ((g : Mat2 K) * ((g⁻¹ : SL(2, K)) : Mat2 K)) * X *
          ((h : Mat2 K) * ((h⁻¹ : SL(2, K)) : Mat2 K))ᵀ := by
          rw [sl_mul_inv, sl_mul_inv]; simp
      _ = _ := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]

@[expose] def twHom (σ : K ≃+* K) : SL(2, K) →* (Mat2 K ≃ₗ[K] Mat2 K) where
  toFun := twEquiv σ
  map_one' := twEquiv_one σ
  map_mul' := twEquiv_mul σ

theorem twHom_apply (σ : K ≃+* K) (s : SL(2, K)) : twHom σ s = twEquiv σ s := rfl

theorem slMap_uSL (σ : K ≃+* K) (a : K) : slMap σ (uSL a) = uSL (σ a) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [coe_slMap]
  fin_cases i <;> fin_cases j <;> simp

@[expose] def tw (σ : K ≃+* K) (c : Fin 2 → K) : Mat2 K :=
  Matrix.vecMulVec c (fun j => σ (c j))

theorem tw_apply (σ : K ≃+* K) (c : Fin 2 → K) (i j : Fin 2) :
    tw σ c i j = c i * σ (c j) := rfl

theorem twEquiv_tw (σ : K ≃+* K) (s : SL(2, K)) (c : Fin 2 → K) :
    twEquiv σ s (tw σ c) = tw σ ((s : Mat2 K) *ᵥ c) := by
  ext i j
  simp only [twEquiv_apply, tw_apply, Matrix.mul_apply, Matrix.transpose_apply, coe_slMap,
    Fin.sum_univ_two, Matrix.mulVec, dotProduct, map_add, map_mul]
  ring

theorem tw_smul (σ : K ≃+* K) (μ : K) (c : Fin 2 → K) :
    tw σ (μ • c) = (μ * σ μ) • tw σ c := by
  ext i j
  simp only [tw_apply, Pi.smul_apply, smul_eq_mul, map_mul, Matrix.smul_apply]
  ring

theorem tw_ne_zero (σ : K ≃+* K) {c : Fin 2 → K} (hc : c ≠ 0) : tw σ c ≠ 0 := by
  intro h
  apply hc
  funext i
  have := congrFun (congrFun h i) i
  simp only [tw_apply, Matrix.zero_apply] at this
  rcases mul_eq_zero.mp this with h1 | h1
  · exact h1
  · have := σ.injective (h1.trans σ.map_zero.symm)
    exact this

@[expose] def polar (X Y : Mat2 K) : K :=
  X 0 0 * Y 1 1 + X 1 1 * Y 0 0 - X 0 1 * Y 1 0 - X 1 0 * Y 0 1

theorem det_add (X Y : Mat2 K) : (X + Y).det = X.det + Y.det + polar X Y := by
  simp only [Matrix.det_fin_two, polar, Matrix.add_apply]
  ring

theorem polar_tw (σ : K ≃+* K) (c c' : Fin 2 → K) :
    polar (tw σ c) (tw σ c') =
      (c 0 * c' 1 - c 1 * c' 0) * σ (c 0 * c' 1 - c 1 * c' 0) := by
  simp only [polar, tw_apply, map_sub, map_mul]
  ring

theorem polar_tw_ne_zero (σ : K ≃+* K) {c c' : Fin 2 → K} (h : c 0 * c' 1 - c 1 * c' 0 ≠ 0) :
    polar (tw σ c) (tw σ c') ≠ 0 := by
  rw [polar_tw]
  refine mul_ne_zero h fun h0 => h (σ.injective ?_)
  rw [h0, σ.map_zero]

theorem tw_single (σ : K ≃+* K) : tw σ (Pi.single 0 1) = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tw_apply, Pi.single_apply]

theorem exists_conj_u [CharP K 2] {t : SL(2, K)} (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    ∃ (g : SL(2, K)) (a : K), a ≠ 0 ∧ t = g * uSL a * g⁻¹ := by
  obtain ⟨p, q, r, s, hK, hdet⟩ := sl2_entries t
  have hmul : ((t * t : SL(2, K)) : Mat2 K) = 1 := by rw [ht2]; rfl
  rw [Matrix.SpecialLinearGroup.coe_mul, hK, Matrix.mul_fin_two, Matrix.one_fin_two,
    sl2_fin_two_eq_iff] at hmul
  obtain ⟨e00, e01, e10, e11⟩ := hmul
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsp : s = p := by
    have h0 : (p - s) * (p - s) = 0 := by
      linear_combination e00 + e11 + (1 - p * s - q * r) * h2K
    exact (sub_eq_zero.mp (mul_self_eq_zero.mp h0)).symm
  subst hsp
  by_cases hr : r = 0
  · have hq : q ≠ 0 := by
      intro hq0
      apply ht1
      have hpp : s * s = 1 := by rw [hr, hq0] at e00; simpa using e00
      have h0 : (s - 1) * (s - 1) = 0 := by linear_combination hpp + (1 - s) * h2K
      have hs1 : s = 1 := sub_eq_zero.mp (mul_self_eq_zero.mp h0)
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [hK, hs1, hq0, hr]
    have hdet' : (!![q, 0; s + 1, q⁻¹] : Mat2 K).det = 1 := by
      rw [Matrix.det_fin_two_of]
      linear_combination mul_inv_cancel₀ hq
    let g : SL(2, K) := ⟨!![q, 0; s + 1, q⁻¹], hdet'⟩
    refine ⟨g, q⁻¹, inv_ne_zero hq, ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    have hss : s * s = 1 := by rw [hr] at e00; simpa using e00
    have key : (t : Mat2 K) * (g : Mat2 K) = (g : Mat2 K) * !![1, q⁻¹; 0, 1] := by
      rw [hK]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [g, Matrix.mul_apply, Fin.sum_univ_two, hr]
      · linear_combination (s * q) * h2K
      · linear_combination hss
      · linear_combination (-q⁻¹) * h2K
    exact Subtype.ext key
  · have hdet' : (!![s + 1, r⁻¹; r, 0] : Mat2 K).det = 1 := by
      rw [Matrix.det_fin_two_of]
      linear_combination (-1 : K) * inv_mul_cancel₀ hr + (-1 : K) * h2K
    let g : SL(2, K) := ⟨!![s + 1, r⁻¹; r, 0], hdet'⟩
    refine ⟨g, r⁻¹, inv_ne_zero hr, ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    have key : (t : Mat2 K) * (g : Mat2 K) = (g : Mat2 K) * !![1, r⁻¹; 0, 1] := by
      rw [hK]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [g, Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination e00
      · linear_combination (-r⁻¹) * h2K
      · linear_combination (r * s) * h2K
    exact Subtype.ext key

theorem fixed_u_singular [CharP K 2] (σ : K ≃+* K) {a : K} (ha : a ≠ 0) {X : Mat2 K}
    (hfix : twEquiv σ (uSL a) X = X) (hdet : X.det = 0) :
    X 0 1 = 0 ∧ X 1 0 = 0 ∧ X 1 1 = 0 := by
  have e : ∀ i j, (twEquiv σ (uSL a) X) i j = X i j := fun i j => by rw [hfix]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  simp only [twEquiv_apply, slMap_uSL, coe_uSL, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    at e00 e01 e10
  have h11 : X 1 1 = 0 :=
    (mul_eq_zero.mp (by linear_combination e01 : a * X 1 1 = 0)).resolve_left ha
  have h10 : a * X 1 0 + σ a * X 0 1 = 0 := by linear_combination e00 - (a * σ a) * h11
  have h0 : X 0 1 * X 1 0 = 0 := by
    rw [Matrix.det_fin_two] at hdet
    linear_combination (-1 : K) * hdet + X 0 0 * h11
  have hσa : σ a ≠ 0 := fun h => ha (σ.injective (h.trans σ.map_zero.symm))
  rcases mul_eq_zero.mp h0 with h | h
  · refine ⟨h, ?_, h11⟩
    rw [h, mul_zero, add_zero] at h10
    exact (mul_eq_zero.mp h10).resolve_left ha
  · refine ⟨?_, h, h11⟩
    rw [h, mul_zero, zero_add] at h10
    exact (mul_eq_zero.mp h10).resolve_left hσa

theorem twEquiv_inv_apply (σ : K ≃+* K) (s : SL(2, K)) (X : Mat2 K) :
    twEquiv σ s⁻¹ (twEquiv σ s X) = X := by
  have h : twHom σ s⁻¹ * twHom σ s = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have := LinearEquiv.congr_fun h X
  simpa [twHom_apply] using this

theorem twEquiv_apply_inv (σ : K ≃+* K) (s : SL(2, K)) (X : Mat2 K) :
    twEquiv σ s (twEquiv σ s⁻¹ X) = X := by
  simpa using twEquiv_inv_apply σ s⁻¹ X

theorem lemmaS [CharP K 2] (σ : K ≃+* K) {t : SL(2, K)} (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    ∃ c : Fin 2 → K, c ≠ 0 ∧ (t : Mat2 K) *ᵥ c = c ∧
      ∀ X : Mat2 K, twEquiv σ t X = X → X.det = 0 → ∃ μ : K, X = μ • tw σ c := by
  obtain ⟨g, a, ha, rfl⟩ := exists_conj_u ht1 ht2
  have he0 : (Pi.single 0 1 : Fin 2 → K) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  set c : Fin 2 → K := (g : Mat2 K) *ᵥ (Pi.single 0 1) with hc
  have hgc : ((g⁻¹ : SL(2, K)) : Mat2 K) *ᵥ c = Pi.single 0 1 := by
    rw [hc, Matrix.mulVec_mulVec, sl_inv_mul, Matrix.one_mulVec]
  refine ⟨c, ?_, ?_, ?_⟩
  · intro h
    apply he0
    rw [← hgc, h, Matrix.mulVec_zero]
  · have hu : (!![1, a; 0, 1] : Mat2 K) *ᵥ (Pi.single 0 1) = Pi.single 0 1 := by
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply]
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgc, hu]
  · intro X hX hdet
    have hY : twEquiv σ (uSL a) (twEquiv σ g⁻¹ X) = twEquiv σ g⁻¹ X := by
      have h1 := hX
      rw [twEquiv_mul, twEquiv_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h1
      have h2 := congrArg (twEquiv σ g⁻¹) h1
      rwa [twEquiv_inv_apply] at h2
    have hYd : (twEquiv σ g⁻¹ X).det = 0 := by rw [det_twEquiv, hdet]
    obtain ⟨h01, h10, h11⟩ := fixed_u_singular σ ha hY hYd
    set Y := twEquiv σ g⁻¹ X with hYdef
    have hYe : Y = (Y 0 0) • tw σ (Pi.single 0 1) := by
      rw [tw_single]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h01, h10, h11]
    refine ⟨Y 0 0, ?_⟩
    have hXY : X = twEquiv σ g Y := by rw [hYdef, twEquiv_apply_inv]
    calc X = twEquiv σ g Y := hXY
      _ = twEquiv σ g ((Y 0 0) • tw σ (Pi.single 0 1)) := by rw [← hYe]
      _ = (Y 0 0) • tw σ c := by rw [map_smul, twEquiv_tw]

theorem exists_sl_mulVec_single {c : Fin 2 → K} (hc : c ≠ 0) :
    ∃ g : SL(2, K), (g : Mat2 K) *ᵥ (Pi.single 0 1) = c := by
  by_cases h0 : c 0 = 0
  · have h1 : c 1 ≠ 0 := by
      intro h
      apply hc
      funext i
      fin_cases i <;> simp [h0, h]
    have hdet : (!![c 0, -(c 1)⁻¹; c 1, 0] : Mat2 K).det = 1 := by
      rw [Matrix.det_fin_two_of]
      field_simp
      ring
    refine ⟨⟨!![c 0, -(c 1)⁻¹; c 1, 0], hdet⟩, ?_⟩
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply]
  · have hdet : (!![c 0, 0; c 1, (c 0)⁻¹] : Mat2 K).det = 1 := by
      rw [Matrix.det_fin_two_of]
      field_simp
      ring
    refine ⟨⟨!![c 0, 0; c 1, (c 0)⁻¹], hdet⟩, ?_⟩
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply]

theorem exists_sl_mulVec_eq {c c' : Fin 2 → K} (hc : c ≠ 0) (hc' : c' ≠ 0) :
    ∃ g : SL(2, K), (g : Mat2 K) *ᵥ c = c' := by
  obtain ⟨g₁, h₁⟩ := exists_sl_mulVec_single hc
  obtain ⟨g₂, h₂⟩ := exists_sl_mulVec_single hc'
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, ← h₁, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    sl_inv_mul, Matrix.mul_one, h₂]

theorem slMap_one (s : SL(2, K)) : slMap (1 : K ≃+* K) s = s := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [coe_slMap]
  rfl

@[expose] def vmvLin (w : Fin 2 → K) : (Fin 2 → K) →ₗ[K] Mat2 K where
  toFun y := Matrix.vecMulVec w y
  map_add' y z := by
    ext i j
    simp [Matrix.vecMulVec_apply, mul_add]
  map_smul' c y := by
    ext i j
    simp [Matrix.vecMulVec_apply, mul_left_comm]

theorem vmvLin_apply (w y : Fin 2 → K) : vmvLin w y = Matrix.vecMulVec w y := rfl

theorem vmvLin_injective {w : Fin 2 → K} (hw : w ≠ 0) : Function.Injective (vmvLin w) := by
  intro y z h
  have h' : Matrix.vecMulVec w (y - z) = 0 := by
    rw [← vmvLin_apply, map_sub, h, sub_self]
  rw [Matrix.vecMulVec_eq_zero] at h'
  rcases h' with h1 | h1
  · exact absurd h1 hw
  · exact sub_eq_zero.mp h1

theorem det_vecMulVec (w y : Fin 2 → K) : (Matrix.vecMulVec w y).det = 0 := by
  simp only [Matrix.det_fin_two, Matrix.vecMulVec_apply]
  ring

theorem range_leftMul [CharP K 2] {g : SL(2, K)} (hg1 : g ≠ 1) (hg2 : g * g = 1) :
    Module.finrank K (LinearMap.range (pairLin ((g : Mat2 K) - 1) 1)) = 2 ∧
      ∀ Y ∈ LinearMap.range (pairLin ((g : Mat2 K) - 1) 1), Y.det = 0 := by
  obtain ⟨g₀, a, ha, rfl⟩ := exists_conj_u hg1 hg2
  have he0 : (Pi.single 0 1 : Fin 2 → K) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  set w : Fin 2 → K := (g₀ : Mat2 K) *ᵥ (Pi.single 0 1) with hw
  have hgw : ((g₀⁻¹ : SL(2, K)) : Mat2 K) *ᵥ w = Pi.single 0 1 := by
    rw [hw, Matrix.mulVec_mulVec, sl_inv_mul, Matrix.one_mulVec]
  have hw0 : w ≠ 0 := by
    intro h
    apply he0
    rw [← hgw, h, Matrix.mulVec_zero]
  have hN : (((g₀ * uSL a * g₀⁻¹ : SL(2, K)) : Mat2 K) - 1) =
      (g₀ : Mat2 K) * !![0, a; 0, 0] * ((g₀⁻¹ : SL(2, K)) : Mat2 K) := by
    have h1 : (1 : Mat2 K) = (g₀ : Mat2 K) * ((g₀⁻¹ : SL(2, K)) : Mat2 K) := (sl_mul_inv g₀).symm
    have h2 : (!![0, a; 0, 0] : Mat2 K) = !![1, a; 0, 1] - 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [h2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, Matrix.mul_assoc]
    conv_lhs => rw [h1]
  have hrange : LinearMap.range (pairLin (((g₀ * uSL a * g₀⁻¹ : SL(2, K)) : Mat2 K) - 1) 1) =
      LinearMap.range (vmvLin w) := by
    rw [hN]
    ext Y
    constructor
    · rintro ⟨X, rfl⟩
      refine ⟨a • (((g₀⁻¹ : SL(2, K)) : Mat2 K) * X) 1, ?_⟩
      ext i j
      simp only [pairLin_apply, Matrix.transpose_one, Matrix.mul_one, vmvLin_apply,
        Matrix.vecMulVec_apply, hw]
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply]
      ring
    · rintro ⟨y, rfl⟩
      refine ⟨(g₀ : Mat2 K) * Matrix.vecMulVec (Pi.single 1 1 : Fin 2 → K) (a⁻¹ • y), ?_⟩
      have h1 : ((g₀ : Mat2 K) * !![0, a; 0, 0] * ((g₀⁻¹ : SL(2, K)) : Mat2 K)) *
          ((g₀ : Mat2 K) * Matrix.vecMulVec (Pi.single 1 1 : Fin 2 → K) (a⁻¹ • y)) =
          (g₀ : Mat2 K) * (!![0, a; 0, 0] *
            Matrix.vecMulVec (Pi.single 1 1 : Fin 2 → K) (a⁻¹ • y)) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc ((g₀⁻¹ : SL(2, K)) : Mat2 K), sl_inv_mul, Matrix.one_mul]
      have h2 : (!![0, a; 0, 0] : Mat2 K) *ᵥ (Pi.single 1 1 : Fin 2 → K) =
          a • (Pi.single 0 1 : Fin 2 → K) := by
        ext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply]
      simp only [pairLin_apply, Matrix.transpose_one, Matrix.mul_one, vmvLin_apply]
      rw [h1, Matrix.mul_vecMulVec, h2, Matrix.mul_vecMulVec, Matrix.mulVec_smul, ← hw]
      ext i j
      simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
  rw [hrange]
  refine ⟨?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj (vmvLin_injective hw0)]
    simp
  · rintro Y ⟨y, rfl⟩
    exact det_vecMulVec w y

theorem exists_ne_zero_ne_one [Finite K] (h4 : 4 ≤ Nat.card K) : ∃ a : K, a ≠ 0 ∧ a ≠ 1 := by
  by_contra h
  push Not at h
  have h2 : Nat.card K ≤ 2 := by
    calc Nat.card K ≤ Nat.card (Fin 2) := by
          refine Nat.card_le_card_of_surjective (fun i : Fin 2 => if i = 0 then (0 : K) else 1) ?_
          intro a
          by_cases ha : a = 0
          · exact ⟨0, by simp [ha]⟩
          · exact ⟨1, by simp [h a ha]⟩
      _ = 2 := by simp
  omega

theorem exists_ne_zero_sq_ne_one [CharP K 2] [Finite K] (h4 : 4 ≤ Nat.card K) :
    ∃ a : K, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  obtain ⟨a, ha0, ha1⟩ := exists_ne_zero_ne_one h4
  refine ⟨a, ha0, fun h => ha1 ?_⟩
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : (a - 1) * (a - 1) = 0 := by linear_combination h + (1 - a) * h2K
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)

theorem sl2_commutator_eq_top [CharP K 2] [Finite K] (h4 : 4 ≤ Nat.card K) :
    commutator SL(2, K) = ⊤ := by
  obtain ⟨a, ha, hasq⟩ := exists_ne_zero_sq_ne_one h4
  exact Matrix.SL2.commutator_eq_top ha hasq

theorem sl2_normal_eq_bot_or_top [CharP K 2] [Finite K] (h4 : 4 ≤ Nat.card K)
    (N : Subgroup SL(2, K)) [hN : N.Normal] : N = ⊥ ∨ N = ⊤ := by
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have hnorm : (N.map (QuotientGroup.mk' (Subgroup.center SL(2, K)))).Normal :=
    Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)
  have hcen : Subgroup.center SL(2, K) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    exact sl2_eq_one_of_central fun A => (Subgroup.mem_center_iff.mp hg A).symm
  haveI := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center SL(2, K)))) with h | h
  · left
    rw [eq_bot_iff]
    intro n hn
    have h1 : QuotientGroup.mk' (Subgroup.center SL(2, K)) n ∈
        N.map (QuotientGroup.mk' (Subgroup.center SL(2, K))) := Subgroup.mem_map_of_mem _ hn
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hcen,
      Subgroup.mem_bot] at h1
    rw [h1]
    exact Subgroup.one_mem _
  · right
    rw [eq_top_iff]
    intro g _
    have h1 : QuotientGroup.mk' (Subgroup.center SL(2, K)) g ∈
        N.map (QuotientGroup.mk' (Subgroup.center SL(2, K))) := by rw [h]; trivial
    obtain ⟨n, hn, hng⟩ := Subgroup.mem_map.mp h1
    have h2 : n⁻¹ * g ∈ Subgroup.center SL(2, K) := by
      rw [← QuotientGroup.eq]
      exact hng
    rw [hcen, Subgroup.mem_bot, inv_mul_eq_one] at h2
    rw [← h2]
    exact hn

@[expose] def slCongr {K K' : Type*} [Field K] [Field K'] (ι : K ≃+* K') :
    SL(2, K) ≃* SL(2, K') :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map (ι : K →+* K'))
    (Matrix.SpecialLinearGroup.map (ι.symm : K' →+* K))
    (by ext A i j; simp [Matrix.SpecialLinearGroup.map_apply_coe])
    (by ext A i j; simp [Matrix.SpecialLinearGroup.map_apply_coe])

theorem slMap_mul (σ τ : K ≃+* K) (A : SL(2, K)) : slMap (σ * τ) A = slMap σ (slMap τ A) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [coe_slMap, coe_slMap, coe_slMap]
  rfl

theorem exists_smul_of_det_zero {c c' : Fin 2 → K} (hc : c ≠ 0)
    (h : c 0 * c' 1 - c 1 * c' 0 = 0) : ∃ s : K, c' = s • c := by
  by_cases h0 : c 0 = 0
  · have h1 : c 1 ≠ 0 := by
      intro h1
      apply hc
      funext i
      fin_cases i <;> simp [h0, h1]
    have h2 : c' 0 = 0 := by
      rw [h0] at h
      have : c 1 * c' 0 = 0 := by linear_combination -h
      exact (mul_eq_zero.mp this).resolve_left h1
    refine ⟨c' 1 / c 1, ?_⟩
    funext i
    fin_cases i
    · simp [h2, h0]
    · simp [div_mul_cancel₀ _ h1]
  · refine ⟨c' 0 / c 0, ?_⟩
    funext i
    fin_cases i
    · simp [div_mul_cancel₀ _ h0]
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination h

theorem card_sl2 [Finite K] : Nat.card SL(2, K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hq : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  rw [Matrix.card_SL_field 2, ← Nat.card_eq_fintype_card]
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  set q := Nat.card K with hqdef
  have h1 : (q ^ 2 - 1) * (q ^ 2 - q) = q * (q ^ 2 - 1) * (q - 1) := by
    have hq1 : 1 ≤ q := by omega
    have hqq : q ≤ q ^ 2 := by nlinarith
    have h1q : 1 ≤ q ^ 2 := by nlinarith
    zify [hq1, hqq, h1q]
    ring
  rw [h1]
  exact Nat.mul_div_cancel _ (by omega)

theorem card_le_of_isPGroup_sl2 [CharP K 2] [Finite K] {P : Subgroup SL(2, K)}
    (hP : IsPGroup 2 P) : Nat.card P ≤ Nat.card K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : Nat.card P ∣ Nat.card SL(2, K) := Subgroup.card_subgroup_dvd_card P
  rw [card_sl2, hk] at hdvd
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hq2 : Even (Nat.card K) := by
    rw [Nat.card_eq_fintype_card, hn]
    exact (Nat.even_pow.mpr ⟨even_two, n.pos.ne'⟩)
  have hq4 : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have hodd : Odd (Nat.card K ^ 2 - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow _ _ (by omega)) (hq2.pow_of_ne_zero (by norm_num)) odd_one
  have hcop : Nat.Coprime (2 ^ k) (Nat.card K ^ 2 - 1) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  have h2 : 2 ^ k ∣ Nat.card K := hcop.dvd_of_dvd_mul_right hdvd
  rw [hk]
  exact Nat.le_of_dvd (by omega) h2

end D2

end CFSG.RankThree.GF2n.Smith81
