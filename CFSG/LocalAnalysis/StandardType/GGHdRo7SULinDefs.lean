module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUDefs

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def SUPInvLeaf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (m : ℕ), 7 ≤ m → ¬ 3 ∣ m → ∀ (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin m) (ZMod p) V) (W : Submodule (ZMod p) V),
    (∀ a, SUPerm p b a → ∀ w ∈ W, a w ∈ W) →
    W = ⊥ ∨ W = Submodule.span (ZMod p) {SUOnes p b} ∨ W = SUAug p b ∨ W = ⊤

@[expose] def SUPCentLeaf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (m : ℕ), 7 ≤ m → ¬ 3 ∣ m → ∀ (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin m) (ZMod p) V) (T : V →ₗ[ZMod p] V),
    (∀ a, SUPerm p b a → T ∘ₗ (a : V →ₗ[ZMod p] V) = (a : V →ₗ[ZMod p] V) ∘ₗ T) →
    ∃ α β : ZMod p, ∀ v, T v = α • v + (β * ∑ i, b.repr v i) • SUOnes p b

@[expose] def SUStabCardLeaf : Prop :=
  SUNormalizerLeaf → ∀ (p : ℕ) [Fact p.Prime] (m : ℕ) (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin m) (ZMod p) V) (H A : Subgroup (V ≃ₗ[ZMod p] V)),
    SULinData p m V b H A →
    Nat.card {a : V ≃ₗ[ZMod p] V // a ∈ H ∧ a (SUOnes p b) = SUOnes p b} ≤ 2 * m.factorial

end CFSG.StandardType.HdRo7SU
