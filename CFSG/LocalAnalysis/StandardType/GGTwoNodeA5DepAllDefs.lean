module

public import CFSG.LocalAnalysis.StandardType.GGDepAFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType

@[expose] def LR6A5DepAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 3 →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Finite V], Module.finrank (ZMod p) V = 6 →
    ∀ (h : Fin (6 - 1) → V) (α : Fin (6 - 1) → Module.Dual (ZMod p) V) (x : V)
      (r : Fin (6 - 1) → (V ≃ₗ[ZMod p] V)),
    GGDepAFrame p 6 h α x → (∀ i v, r i v = v - α i v • h i) →
    ∀ A : Subgroup (V ≃ₗ[ZMod p] V), (∀ i, r i ∈ A) →
      A = Subgroup.closure {s | s ∈ A ∧ GGLinRefl s} →
      (∀ g ∈ A, ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) →
      Nat.card ↥A ≤ p ^ 6 * (6 * (p - 1) * Nat.factorial 6) →
      Nat.card ↥(A ⊓ MulAction.stabilizer (V ≃ₗ[ZMod p] V) x) ≤ (p - 1) * 6 * Nat.factorial 6 →
      ZS.LinWeyl p A ∨
        ∀ s ∈ A, s x ≠ x → ∀ (c : V) (β : Module.Dual (ZMod p) V), (∀ v, s v = v - β v • c) →
          β c = 2 → c ∈ Submodule.span (ZMod p) {x}

end CFSG.StandardType

end
