module

public import CFSG.LocalAnalysis.StandardType.GGDepAFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType

@[expose] def LR6NineAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 3 →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Finite V], Module.finrank (ZMod p) V ≤ 9 →
    ∀ (h : Fin (9 - 1) → V) (α : Fin (9 - 1) → Module.Dual (ZMod p) V) (x : V)
      (r : Fin (9 - 1) → (V ≃ₗ[ZMod p] V)),
    GGDepAFrame p 9 h α x → (∀ i v, r i v = v - α i v • h i) →
    ∀ A : Subgroup (V ≃ₗ[ZMod p] V), (∀ i, r i ∈ A) →
      A = Subgroup.closure {s | s ∈ A ∧ GGLinRefl s} →
      (∀ g ∈ A, ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) →
      Nat.card ↥A ≤ p ^ 9 * (6 * (p - 1) * Nat.factorial 9) →
      Nat.card ↥(A ⊓ MulAction.stabilizer (V ≃ₗ[ZMod p] V) x) ≤ (p - 1) * 6 * Nat.factorial 9 →
      (∃ t ∈ A, GGLinRefl t ∧ t x ≠ x) →
      ZS.LinWeyl p A ∨
        ∃ t ∈ A, GGLinRefl t ∧ t x ≠ x ∧ (∀ g ∈ A, g * t = t * g) ∧
          ∀ s ∈ A, GGLinRefl s → s x ≠ x → s = t

end CFSG.StandardType

end
