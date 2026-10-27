module

public import CFSG.Quasithin.Vol2.Ch11SecAKA6

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1b

open CFSG.Quasithin KGNat

variable {K M : Type} [Field K] [AddCommGroup M] [Module K M]

theorem shape_of_comm_line [CharP K 2] {T : M →+ M} {σ : K →+* K}
    (hσ : ∀ (c : K) (x : M), T (c • x) = σ c • T x) {u₀ u₁ p : M}
    (hind : ∀ c d : K, c • u₀ + d • u₁ = 0 → c = 0 ∧ d = 0) {α β γ : K}
    (h0 : T u₀ = α • u₀) (h1 : T u₁ = β • u₀ + γ • u₁) {k : ℕ} (hk : ∀ x, T^[2 ^ k] x = x)
    (hline : ∀ c d : K, ∃ t : K, T (c • u₀ + d • u₁) - (c • u₀ + d • u₁) = t • p) :
    (∀ c, σ c = c) ∧ α = 1 ∧ γ = 1 := by
  have hTc0 : ∀ c : K, T (c • u₀) = (σ c * α) • u₀ := fun c => by rw [hσ, h0, smul_smul]
  have hTc1 : ∀ d : K, T (d • u₁) = (σ d * β) • u₀ + (σ d * γ) • u₁ := fun d => by
    rw [hσ, h1, smul_add, smul_smul, smul_smul]
  have hα : (∀ c, σ c = c) → α = 1 := by
    intro hσ1
    have hit : ∀ m : ℕ, T^[m] u₀ = α ^ m • u₀ := by
      intro m
      induction m with
      | zero => rw [Function.iterate_zero, id_eq, pow_zero, one_smul]
      | succ m ih => rw [Function.iterate_succ_apply', ih, hTc0, hσ1, pow_succ]
    have h := hit (2 ^ k)
    rw [hk] at h
    have h' : (α ^ 2 ^ k - 1) • u₀ + (0 : K) • u₁ = 0 := by
      rw [zero_smul, add_zero, sub_smul, one_smul, ← h, sub_self]
    exact KA.eq_one_of_pow_two_pow (sub_eq_zero.mp (hind _ _ h').1)
  have hA : ∀ c, σ c * α = c := by
    by_contra hne
    push Not at hne
    obtain ⟨c₀, hc₀⟩ := hne
    obtain ⟨t₀, ht₀⟩ := hline c₀ 0
    rw [zero_smul, add_zero, hTc0, ← sub_smul] at ht₀
    have ht0 : t₀ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ht₀
      exact hc₀ (sub_eq_zero.mp (hind _ 0 (by rw [zero_smul, add_zero]; exact ht₀)).1)
    have hp : p = (t₀⁻¹ * (σ c₀ * α - c₀)) • u₀ := by
      rw [mul_smul, ht₀, smul_smul, inv_mul_cancel₀ ht0, one_smul]
    have hγ : ∀ d, σ d * γ = d := by
      intro d
      obtain ⟨t, ht⟩ := hline 0 d
      rw [zero_smul, zero_add, hTc1, hp, smul_smul] at ht
      have h2 : (σ d * β - t * (t₀⁻¹ * (σ c₀ * α - c₀))) • u₀ + (σ d * γ - d) • u₁ = 0 := by
        rw [sub_smul, sub_smul, ← ht]
        abel
      exact sub_eq_zero.mp (hind _ _ h2).2
    have hγ1 : γ = 1 := by
      have := hγ 1
      rwa [map_one, one_mul] at this
    have hσ1 : ∀ c, σ c = c := fun c => by
      have := hγ c
      rwa [hγ1, mul_one] at this
    exact hc₀ (by rw [hσ1, hα hσ1, mul_one])
  have hα1 : α = 1 := by
    have := hA 1
    rwa [map_one, one_mul] at this
  have hσ1 : ∀ c, σ c = c := fun c => by
    have := hA c
    rwa [hα1, mul_one] at this
  refine ⟨hσ1, hα1, ?_⟩
  have hit : ∀ m : ℕ, ∃ b : K, T^[m] u₁ = b • u₀ + γ ^ m • u₁ := by
    intro m
    induction m with
    | zero => exact ⟨0, by rw [Function.iterate_zero, id_eq, zero_smul, zero_add, pow_zero,
        one_smul]⟩
    | succ m ih =>
      obtain ⟨b, hb⟩ := ih
      refine ⟨b + γ ^ m * β, ?_⟩
      rw [Function.iterate_succ_apply', hb, map_add, hTc0, hTc1, hσ1, hσ1, hα1, mul_one,
        add_smul, pow_succ, mul_comm (γ ^ m) γ, add_assoc]
  obtain ⟨b, hb⟩ := hit (2 ^ k)
  rw [hk] at hb
  have h2 : (-b) • u₀ + (1 - γ ^ 2 ^ k) • u₁ = 0 := by
    calc (-b) • u₀ + (1 - γ ^ 2 ^ k) • u₁ = u₁ - (b • u₀ + γ ^ 2 ^ k • u₁) := by module
      _ = 0 := by rw [← hb, sub_self]
  exact (KA.eq_one_of_pow_two_pow (sub_eq_zero.mp (hind _ _ h2).2).symm)

omit [AddCommGroup M] in
theorem iterate_eq_of_intertwine {W : Type*} [Group W] {f : W → M} {T : M → M} {τ : MulAut W}
    (hT : ∀ w, T (f w) = f (τ w)) (m : ℕ) (w : W) : T^[m] (f w) = f ((τ ^ m) w) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, hT, pow_succ', MulAut.mul_apply]

end CFSG.Quasithin.Vol2.Ch11.SecO1b
