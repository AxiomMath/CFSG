module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def C2CoordModel {G : Type} [Group G] (p : ℕ) (Bs X : Subgroup G) (n : ℕ)
    (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs) : Prop :=
  ∀ a : MulAut ↥Bs, a ∈ ggAutomizer X Bs ↔
    ∃ (σ : Equiv.Perm (Fin (n + 1))) (c : Fin (n + 1) → ZMod p), σ 0 = 0 ∧ c 0 = 1 ∧
      (∀ i, c i = 1 ∨ c i = -1) ∧
      ∀ (f : Fin (n + 1) → Multiplicative (ZMod p)) (i : Fin (n + 1)),
        Multiplicative.toAdd (τ.symm (a (τ f)) (σ i)) = c i * Multiplicative.toAdd (f i)

@[expose] def C2LCoordLeaf : Prop :=
  GGLabelRigidInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGResRowAt ggRowCorank2C p J L →
    ∃ (n : ℕ) (hx : x ∈ Bs) (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs),
      p = 3 ∧ 5 ≤ n ∧ τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p))) = ⟨x, hx⟩ ∧
      C2CoordModel p Bs L n τ

@[expose] def C2KCoordLeaf : Prop :=
  GGLabelRigidInput → GGLBalanceInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGResRowAt ggRowCorank2C p J K →
    ∃ (n : ℕ) (hy : y ∈ Bs) (hx : x ∈ Bs) (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs),
      p = 3 ∧ 5 ≤ n ∧ τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p))) = ⟨y, hy⟩ ∧
      C2CoordModel p Bs K n τ ∧
      ∃ c : ZMod p, ∀ i, Multiplicative.toAdd (τ.symm ⟨x, hx⟩ i) =
        if i = 0 then c else if i = 1 ∨ i = 2 then 1 else 0

end CFSG.StandardType.HdRo7C
