module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGResXDatumAIndep {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs X : Subgroup G) (n : ℕ) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) (e : Fin n ≃ Λ),
    M = (CoxeterMatrix.A n).reindex e ∧ GGIsWeylMatrix M ∧ GGIntCartan M C ∧
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧ (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
      (∃ f : M.Group ≃* ↥(ggAutomizer X Bs), ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧ LinearIndependent (ZMod p) h

@[expose] def GGIndepFixLineLin : Prop :=
  ∀ (p N : ℕ) [Fact p.Prime], p ≠ 2 → 5 ≤ N → p ∣ N →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V], Module.finrank (ZMod p) V ≤ N →
    ∀ (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V)
      (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)),
    LinearIndependent (ZMod p) h → (∀ i j, α i (h j) = (CartanMatrix.A (N - 1) i j : ZMod p)) →
    (∀ i v, r i v = v - α i v • h i) →
    ∀ (ι : Type) [Finite ι] (s : ι → (V ≃ₗ[ZMod p] V)), (∀ i, GGLinRefl (s i)) →
    (SimpleGraph.fromRel fun i j => s i * s j ≠ s j * s i).Connected →
    ∀ (x : V), x ≠ 0 → ggLinFix (Set.range s) = Submodule.span (ZMod p) {x} →
    x ∉ ggLinFix (Set.range r) →
    (∀ g ∈ Subgroup.closure (Set.range r ∪ Set.range s),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) →
    Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)) = 1

@[expose] def GGTwoNodeKFixLineInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (N : ℕ), GGResHyp p B Bs x L D J y K →
    ¬ GGCoxeterForkDatum p Bs L K → ¬ GGCoxeterStdDatum p Bs L K → ¬ GGE6DepPerpCfg p Bs L K →
    GGResRowAt (fun p labJ labK => ggRowTwoNode p labJ labK ∧ labK.rank + 1 = N) p J K →
    p ≠ 2 → 5 ≤ N → N ≤ 10 → p ∣ N → y ∈ K → GGResXDatumAIndep p Bs K (N - 1) →
    ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) ↔ (b : G) ∈ Subgroup.zpowers y

end CFSG.StandardType

end
