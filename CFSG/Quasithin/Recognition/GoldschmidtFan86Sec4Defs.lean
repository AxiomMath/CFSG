module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TArc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

section Seg

variable {V G : Type*} [Group G] [MulAction G V]

@[expose] def PSeg {Γ : SimpleGraph V} (T : Track Γ G) (a b : ℤ) : Prop :=
  a ≤ b ∧ ¬ omega1 (T.subFixer a b) ≤ T.fixer

@[expose] def IsMaxTArc {Γ : SimpleGraph V} (T : Track Γ G) (a b : ℤ) : Prop :=
  IsTArc T a b ∧ ∀ a' b' : ℤ, a' ≤ a → b ≤ b' → IsTArc T a' b' → a' = a ∧ b' = b

end Seg

variable {V : Type*} (Γ : SimpleGraph V) (G : Type*) [Group G] [MulAction G V]

@[expose] def LamSet (a b c : V) : Set (Subgroup G) :=
  {L | ∃ Q : Subgroup G, Q ≠ ⊥ ∧ Q ≤ MulAction.stabilizer G a ⊓ MulAction.stabilizer G b ∧
      L = Subgroup.normalizer (Q : Set G) ∧
      (∀ u v : V, Γ.Adj a u → Γ.Adj a v → ∃ g ∈ L ⊓ MulAction.stabilizer G a, g • u = v) ∧
      (∃ g ∈ L ⊓ MulAction.stabilizer G b, g • a = c)}

@[expose] def LamMax (a b c : V) (L : Subgroup G) : Prop :=
  L ∈ LamSet Γ G a b c ∧ ∀ L' ∈ LamSet Γ G a b c,
    L ⊓ MulAction.stabilizer G a ≤ L' ⊓ MulAction.stabilizer G a →
      L' ⊓ MulAction.stabilizer G a ≤ L ⊓ MulAction.stabilizer G a

end CFSG.Quasithin.Fan86
