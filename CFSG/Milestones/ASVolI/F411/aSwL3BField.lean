module

public import Mathlib.FieldTheory.Finite.Extension

public section

namespace CFSG.ASVolI

variable {K : Type} [Field K]

theorem burnsideF411a_ringEquiv_pow [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (ρ : K ≃+* K) : ∃ j : ℕ, ∀ x : K, ρ x = x ^ (p ^ j) := by
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  let ρ' : K ≃ₐ[ZMod p] K := AlgEquiv.ofRingEquiv (f := ρ) (fun x => by
    have : (ρ.toRingHom).comp (algebraMap (ZMod p) K) = algebraMap (ZMod p) K :=
      RingHom.ext_zmod _ _
    exact congrArg (fun f : ZMod p →+* K => f x) this)
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod p) p K ρ'
  refine ⟨i, fun x => ?_⟩
  have h1 : ρ x = x ^ (Nat.card (ZMod p) ^ i) := hi x
  rwa [Nat.card_zmod] at h1

theorem burnsideF411a_aut_comm [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (σ τ : K ≃+* K) (x : K) : σ (τ x) = τ (σ x) := by
  obtain ⟨i, hi⟩ := burnsideF411a_ringEquiv_pow (p := p) σ
  obtain ⟨j, hj⟩ := burnsideF411a_ringEquiv_pow (p := p) τ
  rw [hi, hj, hj, hi, ← pow_mul, ← pow_mul, mul_comm]

theorem burnsideF411a_pow_cube {p : ℕ} (hp : p % 3 = 1) (x : K) (j : ℕ) :
    ∃ m : K, x ^ (p ^ j) = x * m ^ 3 := by
  have h : p ^ j % 3 = 1 := by simp [Nat.pow_mod, hp]
  refine ⟨x ^ (p ^ j / 3), ?_⟩
  rw [← pow_mul, ← pow_succ']
  congr 1
  have := Nat.div_add_mod (p ^ j) 3
  omega

theorem burnsideF411a_aut_cube [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp : p % 3 = 1)
    (ρ : K ≃+* K) (x : K) : ∃ m : K, ρ x = x * m ^ 3 := by
  obtain ⟨j, hj⟩ := burnsideF411a_ringEquiv_pow (p := p) ρ
  rw [hj]
  exact burnsideF411a_pow_cube hp x j

theorem burnsideF411a_semilinear [Finite K] {s₁ s₂ sZ : K → K}
    (hadd : ∀ a a', s₁ (a + a') = s₁ a + s₁ a')
    (hpair : ∀ a c, sZ (a * c) = -(s₂ c * s₁ a)) (h1 : s₁ 1 ≠ 0) (h2 : s₂ 1 ≠ 0) :
    ∃ τ : K ≃+* K, (∀ a, s₁ a = s₁ 1 * τ a) ∧ ∀ c, s₂ c = s₂ 1 * τ c := by
  have hstar : ∀ x, s₂ 1 * s₁ x = s₂ x * s₁ 1 := by
    intro x
    have ha := hpair x 1
    have hc := hpair 1 x
    rw [mul_one] at ha
    rw [one_mul] at hc
    linear_combination ha - hc
  have hmul : ∀ a c, s₁ (a * c) * s₁ 1 = s₁ a * s₁ c := by
    intro a c
    have e1 := hpair (a * c) 1
    rw [mul_one] at e1
    have e2 := hpair a c
    have e3 : s₂ 1 * s₁ (a * c) = s₂ c * s₁ a := by linear_combination e1 - e2
    have e4 := hstar c
    apply mul_left_cancel₀ h2
    linear_combination s₁ 1 * e3 - s₁ a * e4
  have hzero : s₁ 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    linear_combination -this
  let τr : K →+* K :=
    { toFun := fun x => s₁ x / s₁ 1
      map_one' := div_self h1
      map_mul' := fun x y => by
        field_simp
        linear_combination hmul x y
      map_zero' := by rw [hzero, zero_div]
      map_add' := fun x y => by rw [hadd, add_div] }
  have hinj : Function.Injective τr := τr.injective
  let τ : K ≃+* K := RingEquiv.ofBijective τr ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  have hτ : ∀ x, τ x = s₁ x / s₁ 1 := fun x => rfl
  refine ⟨τ, fun a => ?_, fun c => ?_⟩
  · rw [hτ]
    field_simp
  · rw [hτ]
    have := hstar c
    field_simp
    linear_combination -this

theorem burnsideF411a_class_cube [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp : p % 3 = 1) (σ τ φ : K ≃+* K) {x₀ x₁ x₂ y₀ y₁ y₂ b₁ b₂ : K}
    (hx₀ : x₀ ≠ 0) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0)
    (h1 : y₁ / y₂ * σ b₁ = b₁ * τ (x₀ / x₁)) (h2 : y₀ / y₁ * σ b₂ = b₂ * τ (x₁ / x₂)) :
    ∃ m : K, φ (x₀ * x₁ * x₂) * (y₀ * y₁ * y₂) = m ^ 3 := by
  obtain ⟨k, hk⟩ := burnsideF411a_aut_cube hp φ (x₀ * x₁ * x₂)
  obtain ⟨n₁, hn₁⟩ := burnsideF411a_aut_cube hp τ (x₀ / x₁)
  obtain ⟨n₂, hn₂⟩ := burnsideF411a_aut_cube hp τ (x₁ / x₂)
  obtain ⟨m₁, hm₁⟩ := burnsideF411a_aut_cube hp σ b₁
  obtain ⟨m₂, hm₂⟩ := burnsideF411a_aut_cube hp σ b₂
  have hn₁0 : n₁ ≠ 0 := by
    rintro rfl
    have h0 : τ (x₀ / x₁) = 0 := by rw [hn₁]; ring
    exact div_ne_zero hx₀ hx₁ ((map_eq_zero_iff τ τ.injective).mp h0)
  have hm₂0 : m₂ ≠ 0 := by
    rintro rfl
    have h0 : σ b₂ = 0 := by rw [hm₂]; ring
    exact hb₂ ((map_eq_zero_iff σ σ.injective).mp h0)
  have hm₁0 : m₁ ≠ 0 := by
    rintro rfl
    have h0 : σ b₁ = 0 := by rw [hm₁]; ring
    exact hb₁ ((map_eq_zero_iff σ σ.injective).mp h0)
  rw [hm₁, hn₁] at h1
  rw [hm₂, hn₂] at h2
  have hy₂' : y₂ = y₁ * x₁ * m₁ ^ 3 / (x₀ * n₁ ^ 3) := by
    rw [eq_div_iff (mul_ne_zero hx₀ (pow_ne_zero 3 hn₁0))]
    field_simp at h1
    linear_combination -h1
  have hy₀' : y₀ = y₁ * x₁ * n₂ ^ 3 / (x₂ * m₂ ^ 3) := by
    rw [eq_div_iff (mul_ne_zero hx₂ (pow_ne_zero 3 hm₂0))]
    field_simp at h2
    linear_combination h2
  refine ⟨x₁ * y₁ * k * n₂ * m₁ / (m₂ * n₁), ?_⟩
  rw [hk, hy₂', hy₀']
  field_simp <;> ring

end CFSG.ASVolI
