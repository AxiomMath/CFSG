module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType

structure GGIndepE6Frame {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod p) V) (x : V) : Prop where
  pair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod p)
  indep : LinearIndependent (ZMod p) h
  x_ne : x ≠ 0
  x_ker : ∀ i, α i x = 0
  x_mem : x ∈ Submodule.span (ZMod p) (Set.range h)

@[expose] def LR6E6All : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 3 →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Finite V], Module.finrank (ZMod p) V ≤ 7 →
    ∀ (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod p) V) (x : V)
      (r : Fin 6 → (V ≃ₗ[ZMod p] V)),
    GGIndepE6Frame h α x → (∀ i v, r i v = v - α i v • h i) →
    ∀ A : Subgroup (V ≃ₗ[ZMod p] V), (∀ i, r i ∈ A) →
      A = Subgroup.closure {s | s ∈ A ∧ GGLinRefl s} →
      (∀ g ∈ A, ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) →
      Nat.card ↥A ≤ p ^ 7 * (6 * (p - 1) * 51840) →
      (∃ t ∈ A, GGLinRefl t ∧ t x ≠ x) → ZS.LinWeyl p A

end CFSG.StandardType

end
