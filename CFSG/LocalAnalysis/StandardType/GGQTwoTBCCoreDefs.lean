module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

@[expose] def GGTBCReflCore (X : Type) [Group X] [Finite X] (r : ℕ) : Prop :=
  ∀ H : Subgroup X, CFSG.Open.IsElemAbelian 3 H → Nat.card H = 3 ^ r →
    ∀ d ∈ H, d ≠ 1 →
      ∀ J : Subgroup X, CFSG.Assembly.IsComponentOf J (Subgroup.centralizer {d}) →
        ∀ φ ∈ ggAutomizer (Subgroup.centralizer {d}) H, GGIsReflection 3 φ →
          φ ∈ ggAutomizer J H ∨ ∀ ψ ∈ ggAutomizer J H, φ * ψ = ψ * φ

@[expose] def GGTBCReflCoreIn {G : Type} [Group G] [Finite G] (r : ℕ) (L : Subgroup G) : Prop :=
  ∀ H : Subgroup G, H ≤ L → CFSG.Open.IsElemAbelian 3 H → Nat.card H = 3 ^ r →
    ∀ d ∈ H, d ≠ 1 →
      ∀ J : Subgroup G, CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer {d}) →
        ∀ φ ∈ ggAutomizer (L ⊓ Subgroup.centralizer {d}) H, GGIsReflection 3 φ →
          φ ∈ ggAutomizer J H ∨ ∀ ψ ∈ ggAutomizer J H, φ * ψ = ψ * φ

end CFSG.StandardType

end
