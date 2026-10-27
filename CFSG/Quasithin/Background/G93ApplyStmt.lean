module

public import CFSG.Quasithin.Background.G9StmtsDimensionOnly
public import CFSG.Quasithin.Background.G11BridgeRestrict

public section

namespace CFSG.Quasithin

namespace G11

@[expose] def G93ApplyStmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Γ K H L A : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) (m : ℕ)
    (hKI : Invariant K I) (hHI : Invariant H I),
    IsQuotientOfSQTKTauCeti ↥Γ → K ≤ Γ → H ≤ K → (∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H) →
    IsIrr H I → FaithfulOn H I → A ≤ K → CFSG.Open.IsElemAbelian 2 A → Nat.card ↥A = 2 ^ m →
    FaithfulOn A I → Module.finrank (ZMod 2) I ≤ 2 * (m + 1) →
    CFSG.Open.IsComponentOf L Γ → L ≤ H → (∃ a ∈ A, ∃ l ∈ L, a * l ≠ l * a) →
    (H = L ∨ ∃ L₂ : Subgroup (GLV V), CFSG.Open.IsComponentOf L₂ Γ ∧ L₂ ≠ L ∧ H = L ⊔ L₂ ∧
      ∃ (hL : Invariant L I) (hL₂ : Invariant L₂ I),
        QuasiEquivalent (restrictRange L I hL) (restrictRange L₂ I hL₂)) →
    G93ConclDimensionOnly (restrictRange K I hKI) (restrictRange H I hHI) m

end G11

end CFSG.Quasithin
