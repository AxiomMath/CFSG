module

public import CFSG.Quasithin.H13.AS91Sec3Defs

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH

@[expose] def Stmt3_12_1M24 : Prop :=
  ∀ (l k : Finset (Finset (Fin 24))) (N₁ N₂ : Subgroup S24), IsTrio l → IsTrio k →
    N₁ ≤ M24g → (∀ σ ∈ N₁, σ • l = l) →
    (∀ σ ∈ M24g, σ • l = l → ∀ n ∈ N₁, σ * n * σ⁻¹ ∈ N₁) → IsPGroup 2 N₁ →
    N₂ ≤ M24g → (∀ σ ∈ N₂, σ • k = k) →
    (∀ σ ∈ M24g, σ • k = k → ∀ n ∈ N₂, σ * n * σ⁻¹ ∈ N₂) → IsPGroup 2 N₂ →
    N₁ ⊓ N₂ ≠ ⊥ → Coplanar l k

end CFSG.Quasithin.H13.AS91.M24G
