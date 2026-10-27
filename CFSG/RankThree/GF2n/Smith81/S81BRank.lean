module

public import CFSG.RankThree.GF2n.Smith81.S81BGeom

public section

namespace CFSG.RankThree.GF2n.Smith81.EGeom

section Rank

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

structure MinuscRank (Γ : Subgroup (V ≃ₗ[K] V)) (p₀ : V) (U₀ : Subgroup (V ≃ₗ[K] V))
    (β : V →ₗ[K] V →ₗ[K] K) (n m : ℕ) : Prop where
  β_inv : ∀ g ∈ Γ, ∀ v w : V, β (g v) (g w) = β v w
  β_skew : ∀ v w : V, β v w = - β w v
  W_β : ∀ r ∈ Wsp (Submodule.span K {p₀}) U₀, β p₀ r = 0
  special_exists : ∃ g ∈ Γ, β p₀ (g p₀) = 0 ∧ g p₀ ∉ Wsp (Submodule.span K {p₀}) U₀
  opposite_exists : ∃ g ∈ Γ, β p₀ (g p₀) ≠ 0
  U_card : Nat.card U₀ = Nat.card K ^ (n - 1)
  U_norm : ∀ h ∈ Γ, (∃ c : K, c ≠ 0 ∧ h p₀ = c • p₀) → conjSub h U₀ = U₀
  rank4 : ∀ g₁ ∈ Γ, ∀ g₂ ∈ Γ,
    (g₁ p₀ ∈ Submodule.span K {p₀} ↔ g₂ p₀ ∈ Submodule.span K {p₀}) →
    (g₁ p₀ ∈ Wsp (Submodule.span K {p₀}) U₀ ↔ g₂ p₀ ∈ Wsp (Submodule.span K {p₀}) U₀) →
    (β p₀ (g₁ p₀) = 0 ↔ β p₀ (g₂ p₀) = 0) →
      ∃ h ∈ Γ, (∃ c : K, c ≠ 0 ∧ h p₀ = c • p₀) ∧ ∃ c : K, c ≠ 0 ∧ h (g₁ p₀) = c • g₂ p₀
  U_inter_Q : ∀ g ∈ Γ, g p₀ ∈ Wsp (Submodule.span K {p₀}) U₀ → g p₀ ∉ Submodule.span K {p₀} →
    Nat.card ↥(U₀ ⊓ conjSub g U₀) = Nat.card K ^ (m - 2)
  U_inter_M : ∀ g ∈ Γ, β p₀ (g p₀) = 0 → g p₀ ∉ Wsp (Submodule.span K {p₀}) U₀ →
    Nat.card ↥(U₀ ⊓ conjSub g U₀) = Nat.card K
  U_inter_O : ∀ g ∈ Γ, β p₀ (g p₀) ≠ 0 → Nat.card ↥(U₀ ⊓ conjSub g U₀) = 1

end Rank

end CFSG.RankThree.GF2n.Smith81.EGeom
