module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs

public section

namespace CFSG.StandardType

structure GGDepE6Frame {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod p) V) (x : V) : Prop where
  pair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod p)
  x_ne : x ≠ 0
  x_ker : ∀ i, α i x = 0
  fix : ∀ v, (∀ i, α i v = 0) → v ∈ Submodule.span (ZMod p) {x}
  dep : ¬ LinearIndependent (ZMod p) h

@[expose] def LR6E6DepAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 3 →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Finite V], Module.finrank (ZMod p) V = 6 →
    ∀ (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod p) V) (x : V)
      (r : Fin 6 → (V ≃ₗ[ZMod p] V)),
    GGDepE6Frame h α x → (∀ i v, r i v = v - α i v • h i) →
    ∀ A : Subgroup (V ≃ₗ[ZMod p] V), (∀ i, r i ∈ A) →
      (∀ g ∈ A, ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) →
      Nat.card ↥A ≤ p ^ 6 * (6 * (p - 1) * Nat.factorial 6) →
      ∀ s ∈ A, s x ≠ x → ∀ (c : V) (β : Module.Dual (ZMod p) V), (∀ v, s v = v - β v • c) →
        β c = 2 → c ∈ Submodule.span (ZMod p) {x}

end CFSG.StandardType

end
