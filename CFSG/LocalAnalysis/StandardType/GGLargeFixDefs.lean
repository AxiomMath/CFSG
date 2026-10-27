module

public import CFSG.LocalAnalysis.StandardType.GGResRows
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGResXDatumA
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineStep2Defs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeRowDimDefs
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggRowLargeN (N : ℕ) (p : ℕ) (J X : LargeEvenLabel) : Prop :=
  ggRowTwoNode p J X ∧ 10 ≤ X.rank ∧ X.rank + 1 = N

structure GGLargeLinHyp (p N : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) {T : Type} (s : T → (V ≃ₗ[ZMod p] V)) (x : V) :
    Prop where
  p_ne_two : p ≠ 2
  N_ge : 11 ≤ N
  p_dvd : p ∣ N
  dim_le : Module.finrank (ZMod p) V ≤ N
  pair : ∀ i j, α i (h j) = (CartanMatrix.A (N - 1) i j : ZMod p)
  refl_form : ∀ i v, r i v = v - α i v • h i
  finT : Finite T
  s_refl : ∀ k, GGLinRefl (s k)
  conn : (SimpleGraph.fromRel fun i j => s i * s j ≠ s j * s i).Connected
  x_ne : x ≠ 0
  fix_s : ggLinFix (Set.range s) = Submodule.span (ZMod p) {x}
  x_not_fix : x ∉ ggLinFix (Set.range r)
  no_transv : ∀ g ∈ Subgroup.closure (Set.range r ∪ Set.range s),
    ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)

@[expose] def ggLargeGrp {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {T : Type} (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (s : T → (V ≃ₗ[ZMod p] V)) :
    Subgroup (V ≃ₗ[ZMod p] V) :=
  Subgroup.closure (Set.range r ∪ Set.range s)

@[expose] def GGLargeCardBound (p N : ℕ) (n : ℕ) : Prop :=
  n ≤ p ^ N * (6 * (p - 1) * (2 ^ N * N.factorial))

@[expose] def GGLargeDepFixLineLin : Prop :=
  ∀ (p N : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (T : Type) (s : T → (V ≃ₗ[ZMod p] V)) (x : V),
    GGLargeLinHyp p N h α r s x → ¬ LinearIndependent (ZMod p) h →
    GGLargeCardBound p N (Nat.card ↥(ggLargeGrp r s)) →
    Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)) ≤ 1

@[expose] def GGLargeFixLineLin : Prop :=
  ∀ (p N : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (T : Type) (s : T → (V ≃ₗ[ZMod p] V)) (x : V),
    GGLargeLinHyp p N h α r s x →
    (¬ LinearIndependent (ZMod p) h → GGLargeCardBound p N (Nat.card ↥(ggLargeGrp r s))) →
    Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)) ≤ 1

structure GGLargeDepCase (p N : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) {T : Type} (s : T → (V ≃ₗ[ZMod p] V)) (x : V) :
    Prop where
  lin : GGLargeLinHyp p N h α r s x
  dep : ¬ LinearIndependent (ZMod p) h
  card : GGLargeCardBound p N (Nat.card ↥(ggLargeGrp r s))
  two : 2 ≤ Module.finrank (ZMod p) ↥(ggLinFix (Set.range r))

@[expose] noncomputable def ggLargeRho {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {T : Type} (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V))
    (s : T → (V ≃ₗ[ZMod p] V)) (hA : ggLargeGrp r s ≤ ggLinStab (ggFixLineT r s)) :
    ↥(ggLargeGrp r s) →* (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) :=
  (ggLinRestrictHom (ggFixLineT r s)).comp (Subgroup.inclusion hA)

@[expose] def GGLargeRestr {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {T : Type} (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V))
    (s : T → (V ≃ₗ[ZMod p] V)) (hA : ggLargeGrp r s ≤ ggLinStab (ggFixLineT r s)) : Prop :=
  Function.Injective (ggLargeRho r s hA) ∧ ZS.AbsIrred p (ggLargeRho r s hA).range ∧
    (ggLargeRho r s hA).range =
      Subgroup.closure {q | q ∈ (ggLargeRho r s hA).range ∧ GGLinRefl q}

@[expose] def GGLargeConnected {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {T : Type} (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V))
    (s : T → (V ≃ₗ[ZMod p] V)) : Prop :=
  ∀ a ∈ Set.range r ∪ Set.range s, ∀ b ∈ Set.range r ∪ Set.range s,
    Relation.EqvGen (fun a b => a ∈ Set.range r ∪ Set.range s ∧ b ∈ Set.range r ∪ Set.range s ∧
      GGLinAdj a b) a b

@[expose] def GGLargeRowDimKnown : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (N : ℕ), GGResHyp p B Bs x L D J y K →
    GGResRowAt (ggRowLargeN N) p J K → Nat.card ↥Bs ≤ p ^ N

@[expose] def GGLargeRowNoSevenAtL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (N : ℕ), GGResHyp p B Bs x L D J y K →
    GGResRowAt (ggRowLargeN N) p J K → ¬ GGResRowAt ggRowSeven p J L

@[expose] def GGLargeRowKDatum : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (N : ℕ), GGResHyp p B Bs x L D J y K →
    GGResRowAt (ggRowLargeN N) p J K → 11 ≤ N ∧ p ∣ N ∧ GGResXDatumA p Bs K (N - 1)

@[expose] def GGLargeRowCard : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (N : ℕ), GGResHyp p B Bs x L D J y K →
    GGResRowAt (ggRowLargeN N) p J K →
    GGLargeCardBound p N (Nat.card ↥(ggAutomizer K Bs ⊔ ggAutomizer L Bs))

@[expose] def GGLargeRowFrameInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (N : ℕ), GGResHyp p B Bs x L D J y K →
    GGResRowAt (ggRowLargeN N) p J K → ∀ hx : x ∈ Bs,
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
      (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V)
      (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (T : Type) (s : T → (V ≃ₗ[ZMod p] V)),
      GGLargeLinHyp p N h α r s (ι (Additive.ofMul ⟨x, hx⟩)) ∧
      Subgroup.closure (Set.range r) = (ggAutomizer K Bs).map (ggLin (p := p) ι) ∧
      (¬ LinearIndependent (ZMod p) h → GGLargeCardBound p N (Nat.card ↥(ggLargeGrp r s)))

end CFSG.StandardType

end
