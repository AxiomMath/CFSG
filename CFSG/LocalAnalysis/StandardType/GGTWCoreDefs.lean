module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGTWSurvDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTWCore {G : Type} [Group G] [Finite G] (p N k : ℕ) [Fact p.Prime]
    (Bs L J K : Subgroup G) (pos : GGTWPos) {Λ : Type} [Fintype Λ] [DecidableEq Λ] (b₁ b₂ : Λ)
    {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    (MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa))
    (CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (e : Fin (N - 1) ≃ Λ) (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V)
    (α : Λ ⊕ Λa → Module.Dual (ZMod p) V) (xV : V) : Prop :=
  b₁ ≠ b₂ ∧ Nat.card Λa = k ∧
    (∀ i : Fin (N - 1), ggTWInJ N pos i.val ↔ (e i ≠ b₁ ∧ e i ≠ b₂)) ∧
    GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
    (k = 2 → ∃ eK : Fin (N - 1) ≃ ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa),
      MK = (CoxeterMatrix.A (N - 1)).reindex eK) ∧
    (∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) ∧
    GGDepAFrame p N (fun i => h (Sum.inl (e i))) (fun i => α (Sum.inl (e i))) xV ∧
    (∀ o o' : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa,
      α (o.map Subtype.val id) (h (o'.map Subtype.val id)) = (CK o o' : ZMod p)) ∧
    (∀ g ∈ Subgroup.closure (Set.range fun o => ggLin (p := p) ι (φ o)),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) ∧
    (∃ a : Λa, α (Sum.inr a) xV ≠ 0) ∧
    ggAutomizer L Bs ⊔ ggAutomizer K Bs = Subgroup.closure (Set.range φ) ∧
    ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1))

@[expose] def GGTWUpCfg {G : Type} [Group G] [Finite G] (p N k : ℕ) [Fact p.Prime]
    (Bs L J K : Subgroup G) : Prop :=
  ∃ (pos : GGTWPos) (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (b₁ b₂ : Λ) (Λa : Type)
    (_ : Fintype Λa) (_ : DecidableEq Λa)
    (MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa))
    (CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (e : Fin (N - 1) ≃ Λ) (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V)
    (α : Λ ⊕ Λa → Module.Dual (ZMod p) V) (xV : V),
    GGTWCore p N k Bs L J K pos b₁ b₂ MK CK ι e φ h α xV ∧ Module.finrank (ZMod p) V = N

@[expose] def GGTWLowCfg {G : Type} [Group G] [Finite G] (p N k : ℕ) [Fact p.Prime]
    (Bs L J K : Subgroup G) (x y : G) : Prop :=
  ∃ (pos : GGTWPos) (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (b₁ b₂ : Λ) (Λa : Type)
    (_ : Fintype Λa) (_ : DecidableEq Λa)
    (MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa))
    (CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (e : Fin (N - 1) ≃ Λ) (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V)
    (α : Λ ⊕ Λa → Module.Dual (ZMod p) V) (xV yV : V) (hx : x ∈ Bs) (hy : y ∈ Bs),
    xV = ι (Additive.ofMul ⟨x, hx⟩) ∧ yV = ι (Additive.ofMul ⟨y, hy⟩) ∧
      GGTWCore p N k Bs L J K pos b₁ b₂ MK CK ι e φ h α xV ∧
      Module.finrank (ZMod p) V = N - 1 ∧
      (∀ g ∈ Subgroup.closure (Set.range fun o => ggLin (p := p) ι (φ o)), GGLinRefl g →
        g xV = xV → GGHLLines (ggHLRoots (fun i : Λ => ggLin (p := p) ι (φ (Sum.inl i)))
          (fun i : Λ => h (Sum.inl i))) xV g) ∧
      yV ≠ 0 ∧
      (∀ i : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, ggLin (p := p) ι (φ (Sum.inl i.1)) yV = yV) ∧
      (∀ a : Λa, ggLin (p := p) ι (φ (Sum.inr a)) yV = yV) ∧
      (∀ g ∈ Subgroup.closure (Set.range fun o => ggLin (p := p) ι (φ o)), GGLinRefl g →
        g yV = yV → GGHLLines (ggHLRoots
          (fun o : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa => ggLin (p := p) ι (φ (o.map Subtype.val id)))
          (fun o : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa => h (o.map Subtype.val id))) yV g)

@[expose] def GGTWZKInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    ∀ labJ labK : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labK →
      GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) → GGHasLabel labK (↥K ⧸ Subgroup.center ↥K) →
      (labJ.tag = .A ∨ labJ.tag = .twA) → p ∣ labJ.rank + 3 →
      ¬ ((labK.tag = .A ∧ ¬ p ∣ labK.rank + 1) ∨
        (labK.tag = .twA ∧ ¬ p ∣ labK.rank + 1 ∧ p ∣ 2 ^ labK.n + 1) ∨
        (p = 3 ∧ labK.tag = .D ∧ labK.rank = 4)) →
      GGResSideDatum p Bs K J → ¬ p ∣ Nat.card ↥(Subgroup.center ↥K)

end CFSG.StandardType

end
