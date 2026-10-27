module

public import CFSG.LocalAnalysis.StandardType.GGResLeaves
public import CFSG.LocalAnalysis.StandardType.GGTBWInputDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGWeylSimpleSystemsConjInput : Prop :=
  ∀ (Λ Λ' : Type) [Fintype Λ] [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ']
    (M : CoxeterMatrix Λ) (M' : CoxeterMatrix Λ'), GGIsWeylMatrix M → GGIsWeylMatrix M' →
    ∀ (W : Type) [Group W] (f : M.Group ≃* W) (f' : M'.Group ≃* W),
      (∀ k, ∃ (w : W) (i : Λ), f' (M'.simple k) = w * f (M.simple i) * w⁻¹) →
      ∃ (σ : Λ ≃ Λ') (w : W), ∀ i, f' (M'.simple (σ i)) = w * f (M.simple i) * w⁻¹

@[expose] def GGResXDatum {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs X : Subgroup G) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V),
    GGIsWeylMatrix M ∧ GGIntCartan M C ∧
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧
      (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
      (∃ f : M.Group ≃* ↥(ggAutomizer X Bs), ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ)

@[expose] def GGResSideDatum {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs X J : Subgroup G) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (b : Λ) (M : CoxeterMatrix Λ)
    (C : Matrix Λ Λ ℤ) (MJ : CoxeterMatrix {j : Λ // j ≠ b})
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V),
    GGIsWeylMatrix M ∧ GGIntCartan M C ∧ GGIsWeylMatrix MJ ∧
      (∀ j j' : {j : Λ // j ≠ b}, MJ.M j j' = M.M j j') ∧
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧
      (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
      (∃ f : M.Group ≃* ↥(ggAutomizer X Bs), ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧
      (∃ fJ : MJ.Group ≃* ↥(ggAutomizer J Bs), ∀ j, (fJ (MJ.simple j) : MulAut ↥Bs) = φ j) ∧
      ggAutomizer J Bs = Subgroup.closure (Set.range fun j : {j : Λ // j ≠ b} => φ j) ∧
      GGReflConjSimple p (ggAutomizer J Bs) (fun j : {j : Λ // j ≠ b} => φ j)

@[expose] def GGTBJInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    (GGResXDatum p Bs L → GGResSideDatum p Bs L J ∨ GGResRowAt ggRowNonLevi p J L) ∧
      (GGResXDatum p Bs K → GGResSideDatum p Bs K J ∨ GGResRowAt ggRowNonLevi p J K)

end CFSG.StandardType
