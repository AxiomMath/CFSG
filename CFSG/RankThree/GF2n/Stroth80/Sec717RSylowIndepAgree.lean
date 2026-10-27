module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.PGroup
import Mathlib.LinearAlgebra.Determinant

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Matrix

variable {K : Type*} [Field K]

theorem exists_smul_specialLinearGroup_four [Finite K] [CharP K 2]
    (A : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) :
    ∃ μ : K, μ ≠ 0 ∧ ∃ g : Matrix.SpecialLinearGroup (Fin 4) K, ∀ v, A v = μ • (g • v) := by
  classical
  set Mt : Matrix (Fin 4) (Fin 4) K := LinearMap.toMatrix' (A : (Fin 4 → K) →ₗ[K] (Fin 4 → K))
    with hMt
  have hd : Mt.det ≠ 0 := by
    rw [hMt, LinearMap.det_toMatrix']
    exact A.isUnit_det'.ne_zero
  have hinj : Function.Injective (fun x : K => x ^ 4) := by
    intro x y hxy
    have h : (x - y) ^ 2 ^ 2 = 0 := by
      rw [sub_pow_char_pow, show (2 : ℕ) ^ 2 = 4 by norm_num]
      exact sub_eq_zero.mpr hxy
    exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp h)
  obtain ⟨μ, hμ⟩ := (Finite.injective_iff_surjective.mp hinj) Mt.det
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hd (by simpa using hμ.symm)
  have hdet : (μ⁻¹ • Mt).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, inv_pow]
    simp only at hμ
    rw [hμ, inv_mul_cancel₀ hd]
  let g : Matrix.SpecialLinearGroup (Fin 4) K := ⟨μ⁻¹ • Mt, hdet⟩
  refine ⟨μ, hμ0, g, fun v => ?_⟩
  show A v = μ • ((μ⁻¹ • Mt) *ᵥ v)
  rw [Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hμ0, one_smul, hMt,
    LinearMap.toMatrix'_mulVec]
  rfl

theorem specialLinearGroup_eq_of_smul_eq {n : ℕ} {a b : Matrix.SpecialLinearGroup (Fin n) K}
    (h : ∀ v : Fin n → K, a • v = b • v) : a = b := by
  apply Subtype.ext
  rw [Matrix.ext_iff_mulVec]
  intro v
  have := h v
  rwa [Matrix.SpecialLinearGroup.smul_def, Matrix.SpecialLinearGroup.smul_def,
    Matrix.smul_eq_mulVec, Matrix.smul_eq_mulVec] at this

section Action

variable {X E : Type*} [Group X] [AddCommGroup E] [Module K E]

theorem exists_smul_agree_of_conj [Finite K] [CharP K 2] (φ : X →* (E ≃ₗ[K] E))
    (T : Submodule K E) {Rb : Subgroup X} (η : ↥Rb →* Matrix.SpecialLinearGroup (Fin 4) K)
    (hηs : Function.Surjective η) (hη1 : ∀ r : ↥Rb, η r = 1 → ∀ w ∈ T, φ r w = w)
    (hRT : ∀ r ∈ Rb, ∀ w ∈ T, φ r w ∈ T)
    (hschur : ∀ x : X, (∀ w ∈ T, φ x w ∈ T) →
      (∀ r ∈ Rb, ∀ w ∈ T, φ x (φ r w) = φ r (φ x w)) → ∃ c : K, ∀ w ∈ T, φ x w = c • w)
    {s : X} (hsR : ∀ r ∈ Rb, s * r * s⁻¹ ∈ Rb) (hsT : ∀ w ∈ T, φ s w ∈ T)
    (A : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K))
    (hA : ∀ (r : ↥Rb) (v : Fin 4 → K), A (η r • v) = η ⟨s * r * s⁻¹, hsR r r.2⟩ • A v) :
    ∃ r₀ ∈ Rb, ∃ c : K, ∀ w ∈ T, φ s w = c • φ r₀ w := by
  obtain ⟨μ, hμ0, g, hg⟩ := exists_smul_specialLinearGroup_four A
  obtain ⟨r₀, hr₀⟩ := hηs g
  have key : ∀ r : ↥Rb, η ⟨s * r * s⁻¹, hsR r r.2⟩ = g * η r * g⁻¹ := by
    intro r
    have h1 : η ⟨s * r * s⁻¹, hsR r r.2⟩ * g = g * η r := by
      refine specialLinearGroup_eq_of_smul_eq fun v => ?_
      have h2 := hA r v
      rw [hg, hg, smul_comm (η ⟨s * r * s⁻¹, hsR r r.2⟩) μ] at h2
      have h3 := smul_right_injective (Fin 4 → K) hμ0 h2
      rw [mul_smul, mul_smul]
      exact h3.symm
    rw [← h1, mul_inv_cancel_right]
  set x : X := (r₀ : X)⁻¹ * s with hx
  have hxT : ∀ w ∈ T, φ x w ∈ T := fun w hw => by
    rw [hx, map_mul, LinearEquiv.mul_apply]
    exact hRT _ (Rb.inv_mem r₀.2) _ (hsT w hw)
  have hxR : ∀ r ∈ Rb, ∀ w ∈ T, φ x (φ r w) = φ r (φ x w) := by
    intro r hr w hw
    have hmem : x * r * x⁻¹ * r⁻¹ ∈ Rb := by
      have : x * r * x⁻¹ * r⁻¹ = (r₀ : X)⁻¹ * (s * r * s⁻¹) * r₀ * r⁻¹ := by rw [hx]; group
      rw [this]
      exact Rb.mul_mem (Rb.mul_mem (Rb.mul_mem (Rb.inv_mem r₀.2) (hsR r hr)) r₀.2)
        (Rb.inv_mem hr)
    have hη : η ⟨x * r * x⁻¹ * r⁻¹, hmem⟩ = 1 := by
      have e : (⟨x * r * x⁻¹ * r⁻¹, hmem⟩ : ↥Rb) =
          r₀⁻¹ * ⟨s * r * s⁻¹, hsR r hr⟩ * r₀ * (⟨r, hr⟩ : ↥Rb)⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx]
        group
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, key ⟨r, hr⟩, hr₀]
      group
    have hfix : φ (x * r * x⁻¹ * r⁻¹) (φ r (φ x w)) = φ r (φ x w) :=
      hη1 _ hη (φ r (φ x w)) (hRT r hr _ (hxT w hw))
    have e2 : x * r * x⁻¹ * r⁻¹ * (r * x) = x * r := by group
    have h3 : φ (x * r * x⁻¹ * r⁻¹) (φ r (φ x w)) = φ x (φ r w) := by
      rw [← LinearEquiv.mul_apply (φ r), ← map_mul, ← LinearEquiv.mul_apply, ← map_mul, e2,
        map_mul, LinearEquiv.mul_apply]
    rw [hfix] at h3
    exact h3.symm
  obtain ⟨c, hc⟩ := hschur x hxT hxR
  refine ⟨r₀, r₀.2, c, fun w hw => ?_⟩
  have e : s = (r₀ : X) * x := by rw [hx, mul_inv_cancel_left]
  rw [e, map_mul, LinearEquiv.mul_apply, hc w hw, map_smul]

theorem agree_of_smul_agree_of_isPGroup [CharP K 2] (φ : X →* (E ≃ₗ[K] E))
    (T : Submodule K E) (hT0 : T ≠ ⊥) {Rb : Subgroup X} (hRT : ∀ r ∈ Rb, ∀ w ∈ T, φ r w ∈ T)
    (hscal : ∀ r ∈ Rb, ∀ c : K, (∀ w ∈ T, φ r w = c • w) → c = 1)
    {s r₀ : X} (hs2 : IsPGroup 2 ↥(Subgroup.zpowers s)) (hr₀ : r₀ ∈ Rb) {c : K}
    (h : ∀ w ∈ T, φ s w = c • φ r₀ w) : ∀ w ∈ T, φ s w = φ r₀ w := by
  have hpow : ∀ k : ℕ, ∀ w ∈ T, φ (s ^ k) w = c ^ k • φ (r₀ ^ k) w := by
    intro k
    induction k with
    | zero => intro w _; simp
    | succ k ih =>
      intro w hw
      rw [pow_succ s, pow_succ r₀, map_mul, map_mul, LinearEquiv.mul_apply,
        LinearEquiv.mul_apply, h w hw, map_smul, ih _ (hRT r₀ hr₀ w hw), smul_smul, pow_succ' c]
  obtain ⟨a, ha⟩ := hs2 ⟨s, Subgroup.mem_zpowers s⟩
  have hsa : s ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  obtain ⟨w₀, hw₀T, hw₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT0
  have hfix : ∀ w ∈ T, w = c ^ 2 ^ a • φ (r₀ ^ 2 ^ a) w := fun w hw => by
    have := hpow (2 ^ a) w hw
    rw [hsa, map_one] at this
    exact this
  have hμ0 : c ^ 2 ^ a ≠ 0 := by
    intro h0
    apply hw₀
    rw [hfix w₀ hw₀T, h0, zero_smul]
  have hρ : ∀ w ∈ T, φ (r₀ ^ 2 ^ a) w = (c ^ 2 ^ a)⁻¹ • w := fun w hw => by
    conv_rhs => rw [hfix w hw]
    rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  have hμ : (c ^ 2 ^ a)⁻¹ = 1 := hscal _ (Rb.pow_mem hr₀ _) _ hρ
  have hca : c ^ 2 ^ a = 1 := inv_eq_one.mp hμ
  have hc1 : c = 1 := by
    have h2 : (c - 1) ^ 2 ^ a = 0 := by rw [sub_pow_char_pow, one_pow, hca, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ two_ne_zero)).mp h2)
  intro w hw
  rw [h w hw, hc1, one_smul]

end Action

end CFSG.RankThree.GF2n.Stroth80
