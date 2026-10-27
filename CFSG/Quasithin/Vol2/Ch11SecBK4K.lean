module

public import CFSG.Quasithin.Vol2.Ch11SecBK4E

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin

namespace BK4

theorem card_fix_cube_le {K M : Type} [Field K] [AddCommGroup M] [Module K M] [Finite M]
    (T : M →+ M) (σ : K →+* K) (hT : ∀ (c : K) (x : M), T (c • x) = σ c • T x) {θ : K}
    (h1 : σ θ ≠ θ) (h2 : σ (σ θ) ≠ θ) :
    Nat.card {x : M // T x = x} ^ 3 ≤ Nat.card M := by
  have h3 : σ (σ θ) ≠ σ θ := fun h => h1 (σ.injective h)
  have key : ∀ d₀ d₁ d₂ : M, T d₀ = d₀ → T d₁ = d₁ → T d₂ = d₂ →
      d₀ + θ • d₁ + (θ * θ) • d₂ = 0 → d₂ = 0 ∧ d₁ = 0 ∧ d₀ = 0 := by
    intro d₀ d₁ d₂ e₀ e₁ e₂ hE
    have hT' : ∀ a b : K, T (d₀ + a • d₁ + b • d₂) = d₀ + σ a • d₁ + σ b • d₂ := by
      intro a b
      rw [map_add, map_add, hT, hT, e₀, e₁, e₂]
    have hE1 : d₀ + σ θ • d₁ + (σ θ * σ θ) • d₂ = 0 := by
      have := congrArg T hE
      rwa [hT', map_mul, map_zero] at this
    have hE2 : d₀ + σ (σ θ) • d₁ + (σ (σ θ) * σ (σ θ)) • d₂ = 0 := by
      have := congrArg T hE1
      rwa [hT', map_mul, map_zero] at this
    have hF : ∀ a b : K, a ≠ b → d₀ + a • d₁ + (a * a) • d₂ = 0 →
        d₀ + b • d₁ + (b * b) • d₂ = 0 → d₁ + (a + b) • d₂ = 0 := by
      intro a b hab ha hb
      have h4 : (a - b) • (d₁ + (a + b) • d₂) = 0 := by
        have h5 : (a - b) • (d₁ + (a + b) • d₂) =
            (d₀ + a • d₁ + (a * a) • d₂) - (d₀ + b • d₁ + (b * b) • d₂) := by
          module
        rw [h5, ha, hb, sub_zero]
      exact (smul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hab)
    have hF1 := hF θ (σ θ) (Ne.symm h1) hE hE1
    have hF2 := hF (σ θ) (σ (σ θ)) (Ne.symm h3) hE1 hE2
    have hd₂ : d₂ = 0 := by
      have h4 : (θ - σ (σ θ)) • d₂ = 0 := by
        have h5 : (θ - σ (σ θ)) • d₂ = (d₁ + (θ + σ θ) • d₂) - (d₁ + (σ θ + σ (σ θ)) • d₂) := by
          module
        rw [h5, hF1, hF2, sub_zero]
      exact (smul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr (Ne.symm h2))
    have hd₁ : d₁ = 0 := by
      rw [hd₂, smul_zero, add_zero] at hF1
      exact hF1
    refine ⟨hd₂, hd₁, ?_⟩
    rw [hd₁, hd₂, smul_zero, smul_zero, add_zero, add_zero] at hE
    exact hE
  let ψ : {x : M // T x = x} × {x : M // T x = x} × {x : M // T x = x} → M :=
    fun p => p.1.1 + θ • p.2.1.1 + (θ * θ) • p.2.2.1
  have hψ : Function.Injective ψ := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩, ⟨c', hc'⟩⟩ h
    simp only [ψ] at h
    have hE : (a - a') + θ • (b - b') + (θ * θ) • (c - c') = 0 := by
      rw [smul_sub, smul_sub]
      rw [← sub_eq_zero] at h
      rw [← h]
      abel
    obtain ⟨e₂, e₁, e₀⟩ := key _ _ _ (by rw [map_sub, ha, ha']) (by rw [map_sub, hb, hb'])
      (by rw [map_sub, hc, hc']) hE
    rw [sub_eq_zero] at e₀ e₁ e₂
    subst e₀ e₁ e₂
    rfl
  have h4 := Nat.card_le_card_of_injective ψ hψ
  rwa [Nat.card_prod, Nat.card_prod, ← pow_three] at h4

theorem exists_sigma_sq_ne {K M : Type} [Field K] [AddCommGroup M] [Module K M]
    (T : M →+ M) (σ : K →+* K) (hT : ∀ (c : K) (x : M), T (c • x) = σ c • T x) {p : ℕ}
    (hp2 : Odd p) (hTp : ∀ y, T^[p] y = y) {y₀ : M} (hy₀ : y₀ ≠ 0) (hσ : ∃ θ, σ θ ≠ θ) :
    ∃ θ, σ θ ≠ θ ∧ σ (σ θ) ≠ θ := by
  have hiter : ∀ (k : ℕ) (c : K) (y : M), T^[k] (c • y) = (⇑σ)^[k] c • T^[k] y := by
    intro k
    induction k with
    | zero => intro c y; rfl
    | succ k ih =>
      intro c y
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih, hT]
  have hσp : ∀ c, (⇑σ)^[p] c = c := by
    intro c
    have h1 := hiter p c y₀
    rw [hTp, hTp] at h1
    have h2 : ((⇑σ)^[p] c - c) • y₀ = 0 := by rw [sub_smul, ← h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hy₀)
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  obtain ⟨θ, hθ⟩ := hσ
  have hsq : ∀ c, σ (σ c) = c := by
    intro c
    by_cases hc : σ c = c
    · rw [hc, hc]
    · exact h c hc
  obtain ⟨k, rfl⟩ := hp2
  have h1 : ∀ j : ℕ, (⇑σ)^[2 * j + 1] θ = σ θ := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, Function.iterate_add_apply]
      change (⇑σ)^[2 * j + 1] (σ (σ θ)) = σ θ
      rw [hsq, ih]
  exact hθ ((h1 k).symm.trans (hσp θ))

theorem eq_id_of_iterate_two {M : Type*} (T : M → M) {p : ℕ} (hp2 : Odd p)
    (hTp : ∀ y, T^[p] y = y) (hT2 : ∀ y, T (T y) = y) (y : M) : T y = y := by
  obtain ⟨k, rfl⟩ := hp2
  have h1 : ∀ j : ℕ, ∀ z, T^[2 * j + 1] z = T z := by
    intro j
    induction j with
    | zero => intro z; rfl
    | succ j ih =>
      intro z
      rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, Function.iterate_add_apply]
      change T^[2 * j + 1] (T (T z)) = T z
      rw [hT2, ih]
  rw [← h1 k y, hTp]

variable {G : Type} [Group G] {L V : Subgroup G}

theorem conjV_mem_autOn_of_mem_sup (hLV : L ≤ Subgroup.normalizer (V : Set G)) {x : G}
    (hx : x ∈ L ⊔ Subgroup.centralizer (V : Set G)) (hxV : x ∈ Subgroup.normalizer (V : Set G)) :
    SecA.conjV V x hxV ∈ autOn L V := by
  let S : Subgroup G :=
    { carrier := {y | ∃ hy : y ∈ Subgroup.normalizer (V : Set G), SecA.conjV V y hy ∈ autOn L V}
      mul_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ => by
        refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
        rw [SecA.conjV_mul V ha hb]
        exact Subgroup.mul_mem _ ha' hb'
      one_mem' := ⟨Subgroup.one_mem _, by
        have : SecA.conjV V 1 (Subgroup.one_mem _) = 1 := by
          ext v
          simp [SecA.conjV_apply_coe]
        rw [this]
        exact Subgroup.one_mem _⟩
      inv_mem' := fun {a} ⟨ha, ha'⟩ => by
        refine ⟨Subgroup.inv_mem _ ha, ?_⟩
        rw [SecA.conjV_inv V ha]
        exact Subgroup.inv_mem _ ha' }
  have hLS : L ≤ S := fun l hl => ⟨hLV hl, SecA.conjV_mem_autOn hl (hLV hl)⟩
  have hCS : Subgroup.centralizer (V : Set G) ≤ S := fun c hc => by
    have hcV : c ∈ Subgroup.normalizer (V : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro v
      constructor
      · intro hv
        have h1 : v * c = c * v := Subgroup.mem_centralizer_iff.mp hc v hv
        rw [← h1, mul_inv_cancel_right]
        exact hv
      · intro hv
        have h1 : (c * v * c⁻¹) * c = c * (c * v * c⁻¹) :=
          Subgroup.mem_centralizer_iff.mp hc _ hv
        have h2 : c * v * c⁻¹ = v := by
          have h3 : c * v = c * (c * v * c⁻¹) := by
            calc c * v = c * v * c⁻¹ * c := by group
              _ = c * (c * v * c⁻¹) := h1
          exact (mul_left_cancel h3).symm
        rwa [h2] at hv
    refine ⟨hcV, ?_⟩
    rw [conjV_eq_one_of_mem hcV hc]
    exact Subgroup.one_mem _
  obtain ⟨_, h⟩ := sup_le hLS hCS hx
  exact h

end BK4

end CFSG.Quasithin.Vol2.Ch11.SecB
