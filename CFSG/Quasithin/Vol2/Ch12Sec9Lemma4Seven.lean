module

public import CFSG.Quasithin.Background.G11Stmts

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin

@[expose] def G112ConclSeven : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)),
    G111Hyp B Γ v₁ W X X₀ → IsQuotientOfSQTKTauCeti ↥Γ →
    ∀ N : Subgroup ↥Γ, N.Normal → 7 ∣ Nat.card N →
      (G112Concl6 Γ → Nat.card Γ ≤ 6 * Nat.card N) ∧
      (G11.G112Concl6U33 Γ → Nat.card Γ ≤ 6 * Nat.card N) ∧
      (G112Concl13 Γ → 11 ∣ Nat.card N)

end CFSG.Quasithin.H13
