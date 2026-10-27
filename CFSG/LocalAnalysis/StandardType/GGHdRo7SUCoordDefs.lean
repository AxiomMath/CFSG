module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUDefs

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def SUCoordModel {G : Type} [Group G] (p : ℕ) (Bs X : Subgroup G) (m : ℕ)
    (τ : (Fin m → Multiplicative (ZMod p)) ≃* ↥Bs) : Prop :=
  ∀ a : MulAut ↥Bs, a ∈ ggAutomizer X Bs ↔
    ∃ σ : Equiv.Perm (Fin m), ∀ (f : Fin m → Multiplicative (ZMod p)) (i : Fin m),
      Multiplicative.toAdd (τ.symm (a (τ f)) (σ i)) = Multiplicative.toAdd (f i)

@[expose] def SULCoordLeaf : Prop :=
  GGLabelRigidInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGResRowAt ggRowSUCorank2 p J L →
    ∃ (m : ℕ) (hx : x ∈ Bs) (τ : (Fin m → Multiplicative (ZMod p)) ≃* ↥Bs),
      p = 3 ∧ 7 ≤ m ∧ ¬ 3 ∣ m ∧ τ (fun _ => Multiplicative.ofAdd (1 : ZMod p)) = ⟨x, hx⟩ ∧
      SUCoordModel p Bs L m τ

@[expose] def SUKCoordLeaf : Prop :=
  GGLabelRigidInput → GGLBalanceInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGResRowAt ggRowSUCorank2 p J K →
    ∃ (m : ℕ) (hy : y ∈ Bs) (τ : (Fin m → Multiplicative (ZMod p)) ≃* ↥Bs),
      p = 3 ∧ 7 ≤ m ∧ ¬ 3 ∣ m ∧ τ (fun _ => Multiplicative.ofAdd (1 : ZMod p)) = ⟨y, hy⟩ ∧
      SUCoordModel p Bs K m τ

end CFSG.StandardType.HdRo7SU
