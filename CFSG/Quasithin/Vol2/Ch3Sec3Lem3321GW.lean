module

public import CFSG.Quasithin.EmptyFaithful.S152NWreath

public section

namespace CFSG.Quasithin.H13.L3321

open CFSG.Quasithin.S152N

namespace W3D

noncomputable local instance instFintypeW3D : Fintype W3 :=
  Fintype.ofEquiv _
    (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))).symm

local instance instDecEqW3D : DecidableEq W3 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right) (by
    constructor
    · rintro ⟨h1, h2⟩
      exact RegularWreathProduct.ext h1 h2
    · rintro rfl
      exact ⟨rfl, rfl⟩)

@[expose] def sW (τ : Equiv.Perm (Fin 3)) : W3 := ⟨fun q => if q = 1 then τ else 1, 1⟩

theorem sW_mul_self : ∀ τ : Equiv.Perm (Fin 3), τ * τ = 1 → sW τ * sW τ = 1 := by
  decide +kernel

theorem ofAdd_one_ne : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide

theorem z2_cases (k : Multiplicative (ZMod 2)) : k = 1 ∨ k = Multiplicative.ofAdd 1 := by
  revert k
  decide

theorem ofAdd_one_mul_self : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by
  decide

theorem ofAdd_one_inv : (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ = Multiplicative.ofAdd 1 := by
  decide

theorem ofAdd_one_pow_odd {m : ℕ} (hm : Odd m) :
    Multiplicative.ofAdd (1 : ZMod 2) ^ m = Multiplicative.ofAdd 1 := by
  obtain ⟨j, rfl⟩ := hm
  rw [pow_succ, pow_mul, sq, ofAdd_one_mul_self, one_pow, one_mul]

theorem fact_a : ∀ τ : Equiv.Perm (Fin 3), ∀ w : W3, (∀ q, w.left q = 1 ∨ w.left q = τ) →
    τ * τ = 1 → w * w ≠ 1 → w.right = Multiplicative.ofAdd 1 := by
  decide +kernel

theorem fact_b : ∀ τ : Equiv.Perm (Fin 3), τ * τ = 1 → ∀ r : W3,
    (∀ q, r.left q = 1 ∨ r.left q = τ) → r * r ≠ 1 → ∀ w : W3,
    (∀ q, w.left q = 1 ∨ w.left q = τ) → w * w = 1 → w.right = Multiplicative.ofAdd 1 →
      w = sW τ * r ∨ w = sW τ * r⁻¹ := by
  decide +kernel

theorem fact_c : ∀ τ : Equiv.Perm (Fin 3), τ * τ = 1 → ∀ r : W3,
    (∀ q, r.left q = 1 ∨ r.left q = τ) → r * r ≠ 1 → ∀ w : W3,
    (∀ q, w.left q = 1 ∨ w.left q = τ) → w.right = 1 →
      w = 1 ∨ w = r * r ∨ w = sW τ ∨ w = sW τ * (r * r) := by
  decide +kernel

theorem fact_e : ∀ τ : Equiv.Perm (Fin 3), τ * τ = 1 → τ ≠ 1 → ∀ w : W3,
    (∀ q, w.left q = 1 ∨ w.left q = τ) → w.right = Multiplicative.ofAdd 1 →
      w * w ≠ 1 ∨ (w * sW τ) * (w * sW τ) ≠ 1 := by
  decide +kernel

theorem right_map_eq_one {P : Type} [Group P] (φ : P →* W3) (σ : Monoid.End P)
    {τ : Equiv.Perm (Fin 3)} (hτ : τ * τ = 1) (hτ1 : τ ≠ 1)
    (hK : ∀ x, ∀ q, (φ x).left q = 1 ∨ (φ x).left q = τ)
    {s₁ t₀ : P} (hs₁ : φ s₁ = sW τ) (ht₀ : (φ t₀).right = Multiplicative.ofAdd 1)
    (hσ : ∀ x, φ x = 1 → φ (σ x) = 1) {m : ℕ} (hm : Odd m) (hσm : σ ^ m = 1)
    {x : P} (hx : (φ x).right = 1) : (φ (σ x)).right = 1 := by
  have hpow : ∀ (k : ℕ) (y : P), (σ ^ (k + 1)) y = (σ ^ k) (σ y) := fun k y => by
    rw [pow_succ]
    rfl
  have hσk : ∀ (k : ℕ) (y : P), φ y = 1 → φ ((σ ^ k) y) = 1 := by
    intro k
    induction k with
    | zero => exact fun y hy => hy
    | succ k ih =>
      intro y hy
      rw [pow_succ']
      exact hσ _ (ih y hy)
  have hm1 : 1 ≤ m := by
    obtain ⟨j, rfl⟩ := hm
    omega
  have hback : ∀ (k : ℕ) (y : P), φ ((σ ^ k) y) = 1 → φ y = 1 := by
    intro k y hy
    have h1 : (σ ^ (m * k - k)) ((σ ^ k) y) = y := by
      have e : (σ ^ (m * k - k)) ((σ ^ k) y) = (σ ^ (m * k - k) * σ ^ k) y := rfl
      rw [e, ← pow_add, Nat.sub_add_cancel (Nat.le_mul_of_pos_left k (by omega)), pow_mul,
        hσm, one_pow]
      rfl
    rw [← h1]
    exact hσk _ _ hy
  have hcong : ∀ (k : ℕ) (y z : P), φ y = φ z → φ ((σ ^ k) y) = φ ((σ ^ k) z) := by
    intro k y z hyz
    have h1 : φ (y⁻¹ * z) = 1 := by rw [map_mul, map_inv, hyz, inv_mul_cancel]
    have h2 := hσk k _ h1
    rw [map_mul, map_inv, map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  have hsq : ∀ (k : ℕ) (y : P), φ y * φ y ≠ 1 → φ ((σ ^ k) y) * φ ((σ ^ k) y) ≠ 1 := by
    intro k y hy h1
    apply hy
    rw [← map_mul] at h1 ⊢
    rw [← map_mul] at h1
    exact hback k _ h1
  obtain ⟨r, hr⟩ : ∃ r : P, φ r * φ r ≠ 1 := by
    rcases fact_e τ hτ hτ1 _ (hK t₀) ht₀ with h | h
    · exact ⟨t₀, h⟩
    · exact ⟨t₀ * s₁, by rw [map_mul, hs₁]; exact h⟩
  have hR : ∀ k : ℕ, (φ ((σ ^ k) r)).right = Multiplicative.ofAdd 1 := fun k =>
    fact_a τ _ (hK _) hτ (hsq k r hr)
  have hRinv : ∀ k : ℕ, (φ ((σ ^ k) r⁻¹)).right = Multiplicative.ofAdd 1 := fun k => by
    rw [map_inv, map_inv, RegularWreathProduct.inv_right, hR k]
    exact ofAdd_one_inv
  have hs₁r : (φ s₁).right = 1 := by rw [hs₁]; rfl
  have hs : (φ (σ s₁)).right = 1 := by
    by_contra hne
    have hne' := (z2_cases (φ (σ s₁)).right).resolve_left hne
    have hsq1 : φ (σ s₁) * φ (σ s₁) = 1 := by
      rw [← map_mul, ← map_mul]
      apply hσ
      rw [map_mul, hs₁]
      exact sW_mul_self τ hτ
    have key : ∀ r' : P, (∀ k : ℕ, (φ ((σ ^ k) r')).right = Multiplicative.ofAdd 1) →
        φ (σ s₁) = φ (s₁ * r') → False := by
      intro r' hr' he
      have hk : ∀ k : ℕ, (φ ((σ ^ k) s₁)).right = Multiplicative.ofAdd 1 ^ k := by
        intro k
        induction k with
        | zero => rw [pow_zero, pow_zero]; exact hs₁r
        | succ k ih =>
          rw [hpow, hcong k _ _ he, map_mul, map_mul, RegularWreathProduct.mul_right, ih, hr' k,
            pow_succ]
      have h1 := hk m
      have h2 : (σ ^ m) s₁ = s₁ := by rw [hσm]; rfl
      rw [h2, hs₁r, ofAdd_one_pow_odd hm] at h1
      exact ofAdd_one_ne h1.symm
    rcases fact_b τ hτ _ (hK r) hr _ (hK _) hsq1 hne' with h | h
    · exact key r hR (by rw [h, map_mul, hs₁])
    · exact key r⁻¹ hRinv (by rw [h, map_mul, map_inv, hs₁])
  have hσ1 : ∀ y : P, σ y = (σ ^ 1) y := fun y => by rw [pow_one]
  rcases fact_c τ hτ _ (hK r) hr _ (hK x) hx with h | h | h | h
  · rw [hσ x (by rw [h])]
    rfl
  · have e : φ x = φ (r * r) := by rw [h, map_mul]
    have e2 := hcong 1 _ _ e
    rw [← hσ1, ← hσ1] at e2
    rw [e2, map_mul, map_mul, RegularWreathProduct.mul_right]
    have := hR 1
    rw [← hσ1] at this
    rw [this, ofAdd_one_mul_self]
  · have e : φ x = φ s₁ := by rw [h, hs₁]
    have e2 := hcong 1 _ _ e
    rw [← hσ1, ← hσ1] at e2
    rw [e2]
    exact hs
  · have e : φ x = φ (s₁ * (r * r)) := by rw [h, map_mul, map_mul, hs₁]
    have e2 := hcong 1 _ _ e
    rw [← hσ1, ← hσ1] at e2
    have h1 := hR 1
    rw [← hσ1] at h1
    rw [e2]
    simp only [map_mul, RegularWreathProduct.mul_right]
    rw [hs, h1, ofAdd_one_mul_self, one_mul]

end W3D

end CFSG.Quasithin.H13.L3321
