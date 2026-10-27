module

public import CFSG.RankThree.PartOne.TCX.F4.LayerClaims

public section

namespace CFSG.RankThree.PartOne.TCX.Ree

open Subgroup CFSG
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint (LieModel)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)
open CFSG.RankThree.PartOne.TCX.F4 (LayerClaimsF4)

theorem mem_zpowers_pow_of_two_power {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {d : G} (hd : ∃ k : ℕ, orderOf d = 2 ^ k) : d ∈ Subgroup.zpowers (d ^ p) := by
  obtain ⟨k, hk⟩ := hd
  have hcop : Nat.Coprime p (orderOf d) := by
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  exact Subgroup.mem_zpowers_iff.2 ⟨(m : ℤ), by rw [zpow_natCast]; exact hm⟩

theorem layerClaims_of_pair {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D : Type} [Group D]
    (τ' : D →* D) (hτp : ∀ d, (⇑τ')^[p] d = d)
    (hmodel : ∃ (t' : StatedLieTag) (n' f'' : ℕ), 1 ≤ f'' ∧
      LieModel (D ⧸ Subgroup.center D) t' n' 2 (p * f''))
    {e₁ e₂ : D} (he₁ : τ' e₁ = e₁) (he₂ : τ' e₂ = e₂) (ho₁ : ∃ k : ℕ, orderOf e₁ = 2 ^ k)
    (ho₂ : ∃ k : ℕ, orderOf e₂ = 2 ^ k) (hnc : e₁ * e₂ ≠ e₂ * e₁)
    (h2 : ∀ d₀ : D, d₀ * e₁ = e₁ * d₀ → ∃ k : ℕ, orderOf d₀ = 2 ^ k)
    (hmove : ∃ d : D, τ' d ≠ d) {G : Type} [Group G] (α : MulAut G) (φ : D →* G)
    (hφ : Function.Injective φ) (hαφ : ∀ d, α (φ d) = φ (τ' d)) {Q : Subgroup G}
    (hQ : φ.range = Q) : LayerClaimsF4 p α Q := by
  subst hQ
  refine ⟨?_, ?_, ?_⟩
  ·
    rintro e ⟨d₀, rfl⟩ hin
    have hτ : ∀ d, τ' d = d₀ * d * d₀⁻¹ := by
      intro d
      apply hφ
      rw [← hαφ, hin (φ d) ⟨d, rfl⟩, map_mul, map_mul, map_inv]
    have hit : ∀ (k : ℕ) (d : D), (⇑τ')^[k] d = d₀ ^ k * d * (d₀ ^ k)⁻¹ := by
      intro k
      induction k with
      | zero => intro d; simp
      | succ k ih =>
        intro d
        rw [Function.iterate_succ_apply', ih, hτ, pow_succ']
        group
    have hcomm1 : d₀ * e₁ = e₁ * d₀ := by
      have := hτ e₁
      rw [he₁] at this
      calc d₀ * e₁ = (d₀ * e₁ * d₀⁻¹) * d₀ := by group
        _ = e₁ * d₀ := by rw [← this]
    have hcentp : d₀ ^ p ∈ Subgroup.center D := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := hit p g
      rw [hτp] at this
      calc g * d₀ ^ p = (d₀ ^ p * g * (d₀ ^ p)⁻¹) * d₀ ^ p := by rw [← this]
        _ = d₀ ^ p * g := by group
    have hd₀c : d₀ ∈ Subgroup.center D :=
      (Subgroup.zpowers_le.2 hcentp) (mem_zpowers_pow_of_two_power hp hp2 (h2 d₀ hcomm1))
    obtain ⟨d, hd⟩ := hmove
    apply hd
    rw [hτ d]
    have := Subgroup.mem_center_iff.1 hd₀c d
    calc d₀ * d * d₀⁻¹ = (d₀ * d) * d₀⁻¹ := rfl
      _ = d * d₀ * d₀⁻¹ := by rw [← this]
      _ = d := by group
  · obtain ⟨t', n', f'', hf'', hM⟩ := hmodel
    let e : D ≃* ↥φ.range := MonoidHom.ofInjective hφ
    let e' : D ⧸ Subgroup.center D ≃* ↥φ.range ⧸ Subgroup.center ↥φ.range :=
      QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
    exact ⟨t', n', f'', hf'', lieModel_of_mulEquiv e' hM⟩
  · obtain ⟨k₁, hk₁⟩ := ho₁
    obtain ⟨k₂, hk₂⟩ := ho₂
    refine ⟨φ e₁, ⟨e₁, rfl⟩, by rw [hαφ, he₁], φ e₂, ⟨e₂, rfl⟩, by rw [hαφ, he₂],
      ⟨k₁, ?_⟩, ⟨k₂, ?_⟩, ?_⟩
    · rw [orderOf_injective φ hφ, hk₁]
    · rw [orderOf_injective φ hφ, hk₂]
    · intro h
      rw [← map_mul, ← map_mul] at h
      exact hnc (hφ h)

end CFSG.RankThree.PartOne.TCX.Ree
