module

public import CFSG.Mathlib.GroupTheory.CubeClass
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.StandardType.FF81.CatQ1

open CFSG.LocalAnalysis.ComponentInitial

private def cq1_normOneUnits {F : Type*} [Field F] (σ : F →+* F) : Subgroup Fˣ where
  carrier := {a | σ (a : F) * (a : F) = 1}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    change σ ((a * b : Fˣ) : F) * ((a * b : Fˣ) : F) = 1
    rw [Units.val_mul, map_mul]
    calc σ (a : F) * σ (b : F) * ((a : F) * (b : F))
        = (σ (a : F) * (a : F)) * (σ (b : F) * (b : F)) := by ring
      _ = 1 := by rw [ha, hb, one_mul]
  inv_mem' {a} ha := by
    change σ ((a⁻¹ : Fˣ) : F) * ((a⁻¹ : Fˣ) : F) = 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv_rev, mul_comm (a : F), ha, inv_one]

private lemma cq1_units_pow_three_ne_mk0 {F : Type*} [Field F] {c : F}
    (hc : ∀ x : F, x ^ 3 ≠ c) {hc0 : c ≠ 0} :
    ∀ x : Fˣ, x ^ 3 ≠ (Units.mk0 c hc0 : Fˣ) := by
  intro x hx
  apply hc (x : F)
  have h := congrArg (fun y : Fˣ => (y : F)) hx
  simpa [Units.val_pow_eq_pow_val, Units.val_mk0] using h

theorem exists_cubeData_of_nonCube {F : Type*} [Field F] [Finite F] {c : F}
    (hc : ∀ x : F, x ^ 3 ≠ c) :
    ∃ (lam ω : F) (j : ℕ), ω ^ 3 = 1 ∧ ω ≠ 1 ∧ lam ^ 3 * c ^ j = ω := by
  have hc0 : c ≠ 0 := fun h => hc 0 (by rw [h]; simp)
  let u : Fˣ := Units.mk0 c hc0
  have hu : ∀ x : Fˣ, x ^ 3 ≠ u := cq1_units_pow_three_ne_mk0 hc (hc0 := hc0)
  obtain ⟨ω, hω3, hωne⟩ := IsCyclic.exists_pow_three_eq_one_ne_one (G := Fˣ) hu
  obtain ⟨j, l, -, hl⟩ := IsCyclic.exists_pow_mul_cube (G := Fˣ) hu ω
  refine ⟨(l : F), (ω : F), j, ?_, ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  · intro h
    exact hωne (Units.ext (by simpa using h))
  · have h := congrArg (fun y : Fˣ => (y : F)) hl
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      Units.val_mk0] at h
    rw [mul_comm]
    exact h.symm

theorem exists_cubeData_of_unitary_nonCube {F : Type*} [Field F] [Finite F] (σ : F →+* F) {c : F}
    (hcσ : σ c * c = 1) (hc : ∀ x : F, x ^ 3 ≠ c) :
    ∃ (lam ω : F) (j : ℕ), ω ^ 3 = 1 ∧ ω ≠ 1 ∧ lam ^ 3 * c ^ j = ω ∧
      σ lam * lam = 1 ∧ σ ω * ω = 1 := by
  have hc0 : c ≠ 0 := fun h => hc 0 (by rw [h]; simp)
  let u : Fˣ := Units.mk0 c hc0
  have hu : ∀ x : Fˣ, x ^ 3 ≠ u := cq1_units_pow_three_ne_mk0 hc (hc0 := hc0)
  have huN : u ∈ cq1_normOneUnits σ := hcσ
  have huN' : ∀ x : cq1_normOneUnits σ, x ^ 3 ≠ (⟨u, huN⟩ : cq1_normOneUnits σ) := by
    intro x hx
    apply hu (x : Fˣ)
    have h := congrArg (fun y : cq1_normOneUnits σ => (y : Fˣ)) hx
    simpa using h
  obtain ⟨ωN, hω3, hωne⟩ :=
    IsCyclic.exists_pow_three_eq_one_ne_one (G := cq1_normOneUnits σ) huN'
  obtain ⟨j, lN, -, hl⟩ :=
    IsCyclic.exists_pow_mul_cube (G := cq1_normOneUnits σ) huN' ωN
  refine ⟨((lN : Fˣ) : F), ((ωN : Fˣ) : F), j, ?_, ?_, ?_, lN.2, ωN.2⟩
  · have h1 : ((ωN : Fˣ)) ^ 3 = 1 := by
      have h := congrArg (Subgroup.subtype (cq1_normOneUnits σ)) hω3
      rw [map_pow, map_one] at h
      exact h
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  · intro h
    exact hωne (Subtype.ext (Units.ext (by simpa using h)))
  · have hsub : Subgroup.subtype (cq1_normOneUnits σ) ωN
        = (Subgroup.subtype (cq1_normOneUnits σ) (⟨u, huN⟩ : cq1_normOneUnits σ)) ^ j
          * (Subgroup.subtype (cq1_normOneUnits σ) lN) ^ 3 := by
      rw [hl, map_mul, map_pow, map_pow]
    have hF := congrArg (fun y : Fˣ => (y : F)) hsub
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at hF
    have huval : ((Subgroup.subtype (cq1_normOneUnits σ)
        (⟨u, huN⟩ : cq1_normOneUnits σ)) : F) = c := by
      show (u : F) = c
      exact Units.val_mk0 hc0
    rw [huval] at hF
    rw [mul_comm]
    exact hF.symm

private lemma cq1_four_mul {n : ℕ} {F : Type*} [Field F]
    (X Y Z W : Matrix (Fin n) (Fin n) F) :
    (X * Y) * (Z * W) = X * (Y * Z) * W := by
  calc (X * Y) * (Z * W) = X * (Y * (Z * W)) := Matrix.mul_assoc X Y (Z * W)
    _ = X * ((Y * Z) * W) := by rw [Matrix.mul_assoc Y Z W]
    _ = X * (Y * Z) * W := (Matrix.mul_assoc X (Y * Z) W).symm

private lemma cq1_pow_mul_pow_of_mul_eq_one {n : ℕ} {F : Type*} [Field F]
    {X Y : Matrix (Fin n) (Fin n) F} (h : X * Y = 1) (k : ℕ) : X ^ k * Y ^ k = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hX : X ^ (k + 1) = X * X ^ k := pow_succ' X k
    have hY : Y ^ (k + 1) = Y ^ k * Y := pow_succ Y k
    rw [hX, hY, cq1_four_mul, ih, mul_one, h]

open Matrix in
theorem bar_mul_self_eq_one_of_pow_three_eq_smul {F : Type*} [Field F] (σ : F →+* F) {n : ℕ}
    (hn : 0 < n) {B : Matrix (Fin n) (Fin n) F} (hB : (B.map σ)ᵀ * B = 1) {c : F}
    (hB3 : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F)) : σ c * c = 1 := by
  have hpow : ((B.map σ)ᵀ) ^ 3 * B ^ 3 = 1 := cq1_pow_mul_pow_of_mul_eq_one hB 3
  have hBh3 : ((B.map σ)ᵀ) ^ 3 = σ c • (1 : Matrix (Fin n) (Fin n) F) := by
    calc ((B.map σ)ᵀ) ^ 3 = ((B.map σ) ^ 3)ᵀ := (Matrix.transpose_pow (B.map σ) 3).symm
      _ = ((B ^ 3).map σ)ᵀ := by rw [← Matrix.map_pow]
      _ = ((c • (1 : Matrix (Fin n) (Fin n) F)).map σ)ᵀ := by rw [hB3]
      _ = (σ c • (1 : Matrix (Fin n) (Fin n) F))ᵀ := by
            rw [Matrix.map_smulₛₗ σ σ c (fun a => map_mul σ c a),
              Matrix.map_one σ (map_zero σ) (map_one σ)]
      _ = σ c • (1 : Matrix (Fin n) (Fin n) F) := by simp
  have hscalar : (σ c * c) • (1 : Matrix (Fin n) (Fin n) F) = 1 := by
    have h := hpow
    rw [hBh3, hB3] at h
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul] at h
    exact h
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) F => M ⟨0, hn⟩ ⟨0, hn⟩) hscalar
  simpa using hentry

theorem bar_mul_self_eq_one_of_cube {ℓ f : ℕ} {F : Type*} [Field F] (h : UnitaryFieldData ℓ f F)
    (h3 : 3 ∣ ℓ ^ f + 1) {b : F} (hb : h.bar (b ^ 3) * b ^ 3 = 1) : h.bar b * b = 1 := by
  let t : F := h.bar b * b
  have htbar : h.bar t = t := by
    change h.bar (h.bar b * b) = h.bar b * b
    rw [map_mul, h.bar_bar]
    exact mul_comm b (h.bar b)
  have ht3 : t ^ 3 = 1 := by
    change (h.bar b * b) ^ 3 = 1
    rw [mul_pow, ← map_pow, hb]
  have htne : t ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at ht3
    exact zero_ne_one ht3
  have htq : t ^ (ℓ ^ f) = t := by
    rw [← h.bar_apply t]
    exact htbar
  have htqm1 : t ^ (ℓ ^ f - 1) = 1 := by
    have h' := htq
    rw [show ℓ ^ f = (ℓ ^ f - 1) + 1 by omega, pow_succ] at h'
    exact mul_right_cancel₀ htne (by rw [one_mul]; exact h')
  have hcop : Nat.Coprime 3 (ℓ ^ f - 1) := by
    obtain ⟨k, hk⟩ := h3
    have hq : ℓ ^ f - 1 = 1 + 3 * (k - 1) := by omega
    rw [hq, Nat.coprime_add_mul_left_right]
    simp
  have hdvd3 : orderOf t ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr ht3
  have hdvdq : orderOf t ∣ ℓ ^ f - 1 := orderOf_dvd_iff_pow_eq_one.mpr htqm1
  have hg : orderOf t ∣ Nat.gcd 3 (ℓ ^ f - 1) := Nat.dvd_gcd hdvd3 hdvdq
  rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at hg
  show t = 1
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)

end CFSG.StandardType.FF81.CatQ1
