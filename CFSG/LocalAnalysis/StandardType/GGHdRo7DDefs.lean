module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUDefs

public section

namespace CFSG.StandardType.HdRo7D

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def DSP (p : ℕ) {V : Type} [AddCommGroup V] [Module (ZMod p) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (a : V ≃ₗ[ZMod p] V) : Prop :=
  ∃ (σ : Equiv.Perm (Fin (n + 1))) (c : Fin (n + 1) → ZMod p), σ 0 = 0 ∧ c 0 = 1 ∧
    (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧ ∀ i, a (b i) = c i • b (σ i)

structure DLinData (p : ℕ) [Fact p.Prime] (n : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (H A : Subgroup (V ≃ₗ[ZMod p] V)) : Prop where
  hp : p = 3
  hn : 6 ≤ n
  hPH : ∀ a, DSP p b a → a ∈ H
  hHA : H ≤ A
  hStab : ∀ a ∈ A, a (b 0) = b 0 → ∀ s, DSP p b s → DSP p b (a * s * a⁻¹)
  hNoT : ∀ a ∈ A, ¬ C2Transv p a
  hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ s ∈ S, s ∈ H ∧ GGLinRefl s) ∧ H = Subgroup.closure S ∧
    ∀ s ∈ S, ∀ t ∈ S, Relation.ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ ¬ Commute u v) s t

@[expose] def DNormalizerLeaf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (n : ℕ), 5 ≤ n → ∀ (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (a : V ≃ₗ[ZMod p] V),
    (∀ s, DSP p b s → DSP p b (a * s * a⁻¹)) → a (b 0) = b 0 → C2SP p b a

@[expose] def DFixWeylLeaf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (n : ℕ), 6 ≤ n → ∀ (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (H : Subgroup (V ≃ₗ[ZMod p] V)),
    (∀ a, DSP p b a → a ∈ H) → (∀ a ∈ H, C2SP p b a) → ZS.LinWeyl p H

@[expose] def DReduceULeaf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (H A : Subgroup (V ≃ₗ[ZMod p] V)),
    DLinData p n V b H A → (∀ r ∈ H, GGLinRefl r → ggLinMove r ≤ LinearMap.ker (b.coord 0)) →
    ∀ a ∈ H, a (b 0) = b 0

@[expose] def DReduceVLeaf : Prop :=
  DNormalizerLeaf → ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (H A : Subgroup (V ≃ₗ[ZMod p] V)),
    DLinData p n V b H A → (∃ r ∈ H, GGLinRefl r ∧ ¬ ggLinMove r ≤ LinearMap.ker (b.coord 0)) →
    (∃ a ∈ H, a (b 0) ≠ b 0) →
    ZS.AbsIrred p H ∧ Nat.card H ≤ 6 ^ (n + 1) * (n + 1).factorial

@[expose] def DClassLargeLeaf : Prop :=
  GGReflClassLargeInput' → ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (d : ℕ), 9 ≤ d →
    ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W], Module.finrank (ZMod p) W = d →
    ∀ R : Subgroup (W ≃ₗ[ZMod p] W), ZS.AbsIrred p R →
    R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r} →
    Nat.card R ≤ 6 ^ d * d.factorial → ZS.LinWeyl p R

@[expose] def DLinSmallLeaf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (H A : Subgroup (V ≃ₗ[ZMod p] V)),
    DLinData p n V b H A → (n = 6 ∨ n = 7) →
    (∃ r ∈ H, GGLinRefl r ∧ ¬ ggLinMove r ≤ LinearMap.ker (b.coord 0)) →
    (∃ a ∈ H, a (b 0) ≠ b 0) → ZS.LinWeyl p H

@[expose] def DModelAt {G : Type} [Group G] (p : ℕ) [Fact p.Prime] (Bs X : Subgroup G) (a : G) : Prop :=
  ∃ (n : ℕ) (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (ha : a ∈ Bs),
    p = 3 ∧ ι (Additive.ofMul (⟨a, ha⟩ : ↥Bs)) = b 0 ∧
    ((6 ≤ n ∧ ∀ g, g ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι) ↔ DSP p b g) ∨
      (5 ≤ n ∧ ∀ g, g ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι) ↔ C2SP p b g))

@[expose] def DLModelLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGResRowAt ggRowDCorank2 p J L → DModelAt p Bs L x

@[expose] def DLStabLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
    ∀ [Fact p.Prime], GGResRowAt ggRowDCorank2 p J L → ∀ (hx : x ∈ Bs),
    ∀ ψ ∈ ggAutomizer ⊤ Bs, ψ ⟨x, hx⟩ = ⟨x, hx⟩ →
      ∀ φ ∈ ggAutomizer L Bs, ψ * φ * ψ⁻¹ ∈ ggAutomizer L Bs

@[expose] def DKModelLeaf : Prop :=
  GGLabelRigidInput → GGLBalanceInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGResRowAt ggRowDCorank2 p J K →
    DModelAt p Bs K y ∧ ∀ e ∈ Bs ⊓ Subgroup.centralizer (K : Set G), e ∈ Subgroup.zpowers y

@[expose] def DKStabLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
    ∀ [Fact p.Prime], GGResRowAt ggRowDCorank2 p J K → ∀ (hy : y ∈ Bs),
    (∀ e ∈ Bs ⊓ Subgroup.centralizer (K : Set G), e ∈ Subgroup.zpowers y) →
    ∀ ψ ∈ ggAutomizer ⊤ Bs, ψ ⟨y, hy⟩ = ⟨y, hy⟩ →
      ∀ φ ∈ ggAutomizer K Bs, ψ * φ * ψ⁻¹ ∈ ggAutomizer K Bs

@[expose] def DAJLeaf : Prop :=
  GGResXDichotomyInput → GGTBJInputR → GGLabelRigidInput → GGLBalanceInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    (GGResRowAt ggRowDCorank2 p J L → DModelAt p Bs L x) →
    (GGResRowAt ggRowDCorank2 p J K → DModelAt p Bs K y) →
    (GGResRowAt ggRowDCorank2 p J L ∨ GGResRowAt ggRowDCorank2 p J K) →
    (∃ a ∈ ggAutomizer J Bs, ∃ b ∈ ggAutomizer J Bs, a * b ≠ b * a) ∧
      ggAutomizer J Bs ≤ ggAutomizer L Bs ⊓ ggAutomizer K Bs

end CFSG.StandardType.HdRo7D
