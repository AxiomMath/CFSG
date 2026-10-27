module

public import CFSG.LocalAnalysis.StandardType.GGFrameTBInputs

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly

variable {G : Type} [Group G] {A : Subgroup G} {M' : Type} [Monoid M']

private lemma frameEndN_map_ne_iff (ρ : MulAut ↥A →* M') (hρ : Function.Injective ρ)
    (a b : MulAut ↥A) : ρ a * ρ b ≠ ρ b * ρ a ↔ a * b ≠ b * a := by
  rw [← map_mul, ← map_mul, hρ.ne_iff]

theorem frameConn_image (ρ : MulAut ↥A →* M') (hρ : Function.Injective ρ)
    {𝒜 : Subgroup (MulAut ↥A)} (h : FrameConn 𝒜) :
    ∀ r ∈ ρ '' frameReflSet 𝒜, ∀ t ∈ ρ '' frameReflSet 𝒜,
      Relation.ReflTransGen
        (fun a b => a ∈ ρ '' frameReflSet 𝒜 ∧ b ∈ ρ '' frameReflSet 𝒜 ∧ a * b ≠ b * a) r t := by
  rintro _ ⟨φ, hφ, rfl⟩ _ ⟨ψ, hψ, rfl⟩
  exact (h φ hφ ψ hψ).lift ρ (by
    rintro a b ⟨ha, hb, hab⟩
    exact ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, (frameEndN_map_ne_iff ρ hρ a b).mpr hab⟩)

private lemma frameEndN_nonComm_image (ρ : MulAut ↥A →* M') (hρ : Function.Injective ρ)
    {𝒜 : Subgroup (MulAut ↥A)} {φ : MulAut ↥A} (hφ : φ ∈ frameReflSet 𝒜) :
    frameNonComm 𝒜 φ =
      Set.ncard {t | t ∈ ρ '' frameReflSet 𝒜 ∧ ρ φ * t ≠ t * ρ φ} := by
  have hset : {t | t ∈ ρ '' frameReflSet 𝒜 ∧ ρ φ * t ≠ t * ρ φ}
      = ρ '' {ψ | ψ ∈ frameReflSet 𝒜 ∧ φ * ψ ≠ ψ * φ} := by
    ext t
    constructor
    · rintro ⟨⟨ψ, hψ, rfl⟩, hnc⟩
      exact ⟨ψ, ⟨hψ, (frameEndN_map_ne_iff ρ hρ φ ψ).mp hnc⟩, rfl⟩
    · rintro ⟨ψ, ⟨hψ, hnc⟩, rfl⟩
      exact ⟨⟨ψ, hψ, rfl⟩, (frameEndN_map_ne_iff ρ hρ φ ψ).mpr hnc⟩
  rw [hset, Set.ncard_image_of_injective _ hρ]
  rfl

theorem frameNumIs_image (ρ : MulAut ↥A →* M') (hρ : Function.Injective ρ)
    {𝒜 : Subgroup (MulAut ↥A)} {N : ℕ} {d : Option ℕ} (h : FrameNumIs 𝒜 N d) {d' : ℕ}
    (hd' : ∀ r ∈ ρ '' frameReflSet 𝒜,
      Set.ncard {t | t ∈ ρ '' frameReflSet 𝒜 ∧ r * t ≠ t * r} = d')
    (hne : (frameReflSet 𝒜).Nonempty) :
    (ρ '' frameReflSet 𝒜).ncard = N ∧ d = some d' := by
  have hcard : (ρ '' frameReflSet 𝒜).ncard = (frameReflSet 𝒜).ncard :=
    Set.ncard_image_of_injective _ hρ
  constructor
  · rw [hcard]; exact h.1
  · rcases hne with ⟨φ₀, hφ₀⟩
    have hnc₀ : frameNonComm 𝒜 φ₀ = d' := by
      rw [frameEndN_nonComm_image ρ hρ hφ₀]
      exact hd' (ρ φ₀) ⟨φ₀, hφ₀, rfl⟩
    cases d with
    | none =>
        exfalso
        exact h.2 ⟨d', fun φ hφ => by
          rw [frameEndN_nonComm_image ρ hρ hφ]
          exact hd' (ρ φ) ⟨φ, hφ, rfl⟩⟩
    | some d₀ =>
        have hd₀ : frameNonComm 𝒜 φ₀ = d₀ := h.2 φ₀ hφ₀
        rw [← hd₀, hnc₀]

end CFSG.StandardType.FrameRoute

end
