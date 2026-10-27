module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType

@[expose] def LR6A5All : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 3 →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Finite V], Module.finrank (ZMod p) V ≤ 6 →
    ∀ (h : Fin (6 - 1) → V) (α : Fin (6 - 1) → Module.Dual (ZMod p) V) (x : V)
      (r : Fin (6 - 1) → (V ≃ₗ[ZMod p] V)),
    GGIndepAFrame p 6 h α x → (∀ i v, r i v = v - α i v • h i) →
    ∀ A : Subgroup (V ≃ₗ[ZMod p] V), (∀ i, r i ∈ A) →
      A = Subgroup.closure {s | s ∈ A ∧ GGLinRefl s} →
      (∀ g ∈ A, ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) →
      Nat.card ↥A ≤ p ^ 6 * (6 * (p - 1) * Nat.factorial 6) →
      (∃ t ∈ A, GGLinRefl t ∧ t x ≠ x) → ZS.LinWeyl p A

end CFSG.StandardType

end
