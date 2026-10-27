module

public import CFSG.LocalAnalysis.StandardType.GGResLeaves
public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeDefs
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGResXDatumA
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrDefs
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggRowTwoNodeLargeLK (p : ℕ) (J X : LargeEvenLabel) : Prop :=
  ggRowTwoNode p J X ∧ (if p = 3 then 8 else 9) ≤ X.rank

@[expose] def ggRowTwoNodeSmallLK (p : ℕ) (J X : LargeEvenLabel) : Prop :=
  ggRowTwoNode p J X ∧ X.rank < (if p = 3 then 8 else 9)

theorem GGResRowAt.twoNode_splitLK {G : Type} [Group G] {p : ℕ} {J X : Subgroup G}
    (h : GGResRowAt ggRowTwoNode p J X) :
    GGResRowAt ggRowTwoNodeLargeLK p J X ∨ GGResRowAt ggRowTwoNodeSmallLK p J X := by
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hr⟩ := h
  by_cases h' : (if p = 3 then 8 else 9) ≤ labX.rank
  · exact Or.inl ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, ⟨hr, h'⟩⟩
  · exact Or.inr ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, ⟨hr, by omega⟩⟩

@[expose] def GGResTwoNodeIndepLargeInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ _ x L _ J y K =>
    (GGResRowAt ggRowTwoNodeLargeLK p J L ∧ x ∈ L) ∨ (GGResRowAt ggRowTwoNodeLargeLK p J K ∧ y ∈ K)

@[expose] def GGResTwoNodeIndepSmallInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ _ x L _ J y K =>
    (GGResRowAt ggRowTwoNodeSmallLK p J L ∧ x ∈ L) ∨ (GGResRowAt ggRowTwoNodeSmallLK p J K ∧ y ∈ K)

@[expose] def ggRowTwoNodeSmallA (p : ℕ) (J X : LargeEvenLabel) : Prop :=
  ggRowTwoNodeSmallLK p J X ∧ (X.tag = .A ∨ X.tag = .twA)

@[expose] def ggRowTwoNodeSmallE6 (p : ℕ) (J X : LargeEvenLabel) : Prop :=
  ggRowTwoNodeSmallLK p J X ∧ (X.tag = .E6 ∨ X.tag = .twE6)

theorem GGResRowAt.smallLK_split {G : Type} [Group G] {p : ℕ} {J X : Subgroup G}
    (h : GGResRowAt ggRowTwoNodeSmallLK p J X) :
    GGResRowAt ggRowTwoNodeSmallA p J X ∨ GGResRowAt ggRowTwoNodeSmallE6 p J X := by
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, hr⟩ := h
  rcases hr.1 with ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩ | ⟨-, -, -, hX⟩
  · exact Or.inl ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, ⟨hr, Or.inl (by rw [hX])⟩⟩
  · exact Or.inl ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, ⟨hr, Or.inr (by rw [hX])⟩⟩
  · exact Or.inr ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, ⟨hr, Or.inl (by rw [hX])⟩⟩
  · exact Or.inr ⟨labJ, labX, hJΛ, hXΛ, hJl, hXl, ⟨hr, Or.inr (by rw [hX])⟩⟩

@[expose] def GGResTwoNodeIndepSmallRestInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs x L _ J y K =>
    (GGResRowAt ggRowTwoNodeSmallE6 p J L ∧ x ∈ L) ∨ (GGResRowAt ggRowTwoNodeSmallE6 p J K ∧ y ∈ K) ∨
    (GGResRowAt ggRowTwoNodeSmallA p J L ∧ x ∈ L ∧ ¬ GGResSideDatum p Bs K J) ∨
    (GGResRowAt ggRowTwoNodeSmallA p J K ∧ y ∈ K ∧ ¬ GGResSideDatum p Bs L J)

@[expose] def GGResTwoNodeIndepSmallTwoInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs x L _ J y K =>
    (GGResRowAt ggRowTwoNodeSmallE6 p J L ∧ x ∈ L) ∨ (GGResRowAt ggRowTwoNodeSmallE6 p J K ∧ y ∈ K) ∨
    (GGResRowAt ggRowTwoNodeSmallA p J L ∧ x ∈ L ∧ GGResTwoNodeSideDatum p Bs K J) ∨
    (GGResRowAt ggRowTwoNodeSmallA p J K ∧ y ∈ K ∧ GGResTwoNodeSideDatum p Bs L J)

@[expose] def ggBstarComm {G : Type} [Group G] (X Bs : Subgroup G) : Subgroup ↥Bs :=
  Subgroup.closure {c | ∃ (b : ↥Bs) (φ : MulAut ↥Bs), φ ∈ ggAutomizer X Bs ∧ c = b⁻¹ * φ b}

@[expose] def ggRowTwoNodeNine (p : ℕ) (J X : LargeEvenLabel) : Prop :=
  ggRowTwoNode p J X ∧ p = 3 ∧ X.rank = 8

@[expose] def GGResTwoNodeNineDepInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs x L _ J y K =>
    (GGResRowAt ggRowTwoNodeNine p J L ∧ x ∈ L ∧ x ∉ (ggBstarComm L Bs).map Bs.subtype) ∨
    (GGResRowAt ggRowTwoNodeNine p J K ∧ y ∈ K ∧ y ∉ (ggBstarComm K Bs).map Bs.subtype)

@[expose] def GGResTwoNodeNineDepTwoInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs x L _ J y K =>
    (GGResRowAt ggRowTwoNodeNine p J L ∧ x ∈ L ∧ x ∉ (ggBstarComm L Bs).map Bs.subtype ∧
      GGResTwoNodeSideDatum p Bs K J) ∨
    (GGResRowAt ggRowTwoNodeNine p J K ∧ y ∈ K ∧ y ∉ (ggBstarComm K Bs).map Bs.subtype ∧
      GGResTwoNodeSideDatum p Bs L J)

@[expose] def GGResXDatumAx {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs X : Subgroup G) (x : G) (n : ℕ) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) (e : Fin n ≃ Λ),
    M = (CoxeterMatrix.A n).reindex e ∧ GGIsWeylMatrix M ∧ GGIntCartan M C ∧
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧ (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
      (∃ f : M.Group ≃* ↥(ggAutomizer X Bs), ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧
      (x ∈ X → LinearIndependent (ZMod p) h)

@[expose] def GGResXDatumE6x {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs X : Subgroup G) (x : G) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) (e : Fin 6 ≃ Λ),
    M = CoxeterMatrix.E₆.reindex e ∧ GGIsWeylMatrix M ∧ GGIntCartan M C ∧
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧ (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
      (∃ f : M.Group ≃* ↥(ggAutomizer X Bs), ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧
      (x ∈ X → LinearIndependent (ZMod p) h)

@[expose] def GGTwoNodeIndepDatum : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    ∀ (X : Subgroup G) (z : G), (X = L ∧ z = x) ∨ (X = K ∧ z = y) →
      ∀ labJ labX : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labX →
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) → GGHasLabel labX (↥X ⧸ Subgroup.center ↥X) →
        ggRowTwoNode p labJ labX → z ∈ X →
        (((labX.tag = .A ∨ labX.tag = .twA) ∧
            (GGResXDatumAx p Bs X z labX.rank ∨
              (p ^ 2 ∣ Nat.gcd (labX.rank + 1) (ggTorM labX) ∧ GGResXDatumA p Bs X labX.rank))) ∨
          ((labX.tag = .E6 ∨ labX.tag = .twE6) ∧ GGResXDatumE6x p Bs X z))

structure GGIndepAFrame (p N : ℕ) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V) (x : V) : Prop where
  pair : ∀ i j, α i (h j) = (CartanMatrix.A (N - 1) i j : ZMod p)
  dvd : p ∣ N
  indep : LinearIndependent (ZMod p) h
  x_ne : x ≠ 0
  x_ker : ∀ i, α i x = 0
  x_mem : x ∈ Submodule.span (ZMod p) (Set.range h)
  fix : ∀ v, (∀ i, α i v = 0) → v ∈ Submodule.span (ZMod p) {x}

end CFSG.StandardType

end
