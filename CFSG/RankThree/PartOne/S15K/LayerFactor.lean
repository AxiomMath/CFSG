module

public import CFSG.RankThree.PartOne.S15K.LayerInner

public section

namespace CFSG.RankThree.PartOne.S15K

variable {G : Type*} [Group G] {Γ : Type*} [Group Γ]

theorem exists_mul_of_mem_iSup_of_commute {U : Type*} [Group U] {ι : Type*} (F : ι → Subgroup U)
    (i : ι) (hcomm : ∀ j, F j ≠ F i → ∀ u ∈ F i, ∀ v ∈ F j, u * v = v * u) {k : U}
    (hk : k ∈ ⨆ j, F j) :
    ∃ X ∈ F i, ∃ k' : U, (∀ f ∈ F i, k' * f = f * k') ∧ k = X * k' := by
  refine Subgroup.iSup_induction F (C := fun k => ∃ X ∈ F i, ∃ k' : U,
    (∀ f ∈ F i, k' * f = f * k') ∧ k = X * k') hk ?_ ?_ ?_
  · intro j k hk
    by_cases hj : F j = F i
    · rw [hj] at hk
      exact ⟨k, hk, 1, fun f _ => by simp, by simp⟩
    · exact ⟨1, one_mem _, k, fun f hf => (hcomm j hj f hf k hk).symm, by simp⟩
  · exact ⟨1, one_mem _, 1, fun f _ => by simp, by simp⟩
  · rintro a b ⟨X₁, hX₁, k₁, hk₁, rfl⟩ ⟨X₂, hX₂, k₂, hk₂, rfl⟩
    refine ⟨X₁ * X₂, mul_mem hX₁ hX₂, k₁ * k₂, fun f hf => ?_, ?_⟩
    · rw [mul_assoc, hk₂ f hf, ← mul_assoc, hk₁ f hf, mul_assoc]
    · have hc : k₁ * X₂ = X₂ * k₁ := hk₁ X₂ hX₂
      calc X₁ * k₁ * (X₂ * k₂) = X₁ * (k₁ * X₂) * k₂ := by group
        _ = X₁ * (X₂ * k₁) * k₂ := by rw [hc]
        _ = X₁ * X₂ * (k₁ * k₂) := by group

theorem exists_mul_mem_centralizer_of_factor {I : Subgroup G} (ψ : ↥I →* Γ)
    (hψ : Function.Injective ψ) {U : Type*} [Group U] (ρ : U →* Γ) {ι : Type*}
    (F : ι → Subgroup U) (i : ι) {Q : Subgroup G}
    (hQ : ∀ x : G, x ∈ Q ↔ ∃ hx : x ∈ I, ψ ⟨x, hx⟩ ∈ (F i).map ρ)
    (hFB : (F i).map ρ ≤ ψ.range)
    (hJcomm : ∀ j, (F j).map ρ ≠ (F i).map ρ → ∀ u ∈ (F i).map ρ, ∀ v ∈ (F j).map ρ,
      u * v = v * u) {e : G} (he : e ∈ Subgroup.normalizer (I : Set G)) {m z k : U}
    (hcompat : ∀ x : ↥I, ψ (I.normalizerMonoidHom ⟨e, he⟩ x) = ρ m * ψ x * (ρ m)⁻¹)
    (hm : m = z * k) (hz : ∀ f ∈ F i, z * f = f * z) (hk : k ∈ ⨆ j, F j) :
    ∃ x ∈ Q, ∃ y ∈ Subgroup.centralizer (Q : Set G), e = x * y := by
  have hρk : ρ k ∈ ⨆ j, (F j).map ρ := by
    rw [← Subgroup.map_iSup]
    exact ⟨k, hk, rfl⟩
  obtain ⟨X', hX', k', hk', hρkeq⟩ :=
    exists_mul_of_mem_iSup_of_commute (fun j => (F j).map ρ) i hJcomm hρk
  refine exists_mul_mem_centralizer_of_decomp' ψ hψ hQ hFB he hcompat (X := X')
    (y := ρ z * k') ?_ hX' fun f hf => ?_
  · rw [hm, map_mul, hρkeq]
    obtain ⟨X, hX, rfl⟩ := hX'
    have : ρ z * ρ X = ρ X * ρ z := by rw [← map_mul, ← map_mul, hz X hX]
    calc ρ z * (ρ X * k') = (ρ z * ρ X) * k' := by group
      _ = ρ X * ρ z * k' := by rw [this]
      _ = ρ X * (ρ z * k') := by group
  · obtain ⟨f₀, hf₀, rfl⟩ := hf
    have h1 : ρ z * ρ f₀ = ρ f₀ * ρ z := by rw [← map_mul, ← map_mul, hz f₀ hf₀]
    rw [mul_assoc, hk' (ρ f₀) ⟨f₀, hf₀, rfl⟩, ← mul_assoc, h1, mul_assoc]

end CFSG.RankThree.PartOne.S15K
