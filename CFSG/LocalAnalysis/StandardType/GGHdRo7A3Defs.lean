module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUDefs

public section

namespace CFSG.StandardType.HdRo7A3

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def a3Aug (p m : ℕ) : Submodule (ZMod p) (Fin m → ZMod p) where
  carrier := {u | ∑ i, u i = 0}
  add_mem' := by
    intro u v hu hv
    change ∑ i, u i = 0 at hu
    change ∑ i, v i = 0 at hv
    change ∑ i, (u + v) i = 0
    simp only [Pi.add_apply, Finset.sum_add_distrib, hu, hv, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c u hu
    change ∑ i, u i = 0 at hu
    change ∑ i, (c • u) i = 0
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hu, mul_zero]

@[expose] def A3Frame (p m : ℕ) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (θ : (Fin m → ZMod p) →ₗ[ZMod p] V) (z : V) : Prop :=
  (∀ u ∈ a3Aug p m, θ u = 0 → ∃ c : ZMod p, u = fun _ => c) ∧
    (∀ v : V, ∃ u ∈ a3Aug p m, ∃ c : ZMod p, v = θ u + c • z) ∧
    ((θ (fun _ => 1) = z ∧ z ≠ 0) ∨ (θ (fun _ => 1) = 0 ∧ ∀ u ∈ a3Aug p m, θ u ≠ z))

@[expose] def A3P (p m : ℕ) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (θ : (Fin m → ZMod p) →ₗ[ZMod p] V) (z : V) (a : V ≃ₗ[ZMod p] V) : Prop :=
  ∃ σ : Equiv.Perm (Fin m),
    (∀ u ∈ a3Aug p m, a (θ u) = θ (fun i => u (σ.symm i))) ∧ a z = z

structure A3LinData (p : ℕ) [Fact p.Prime] (m : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    (θ : (Fin m → ZMod p) →ₗ[ZMod p] V) (z : V) (H A : Subgroup (V ≃ₗ[ZMod p] V)) : Prop where
  hp : p = 3
  hm : 9 ≤ m
  h3 : 3 ∣ m
  hfr : A3Frame p m θ z
  hPH : ∀ a, A3P p m θ z a → a ∈ H
  hHA : H ≤ A
  hStab : ∀ a ∈ A, a z = z → ∀ s, A3P p m θ z s → A3P p m θ z (a * s * a⁻¹)
  hNoT : ∀ a ∈ A, ¬ C2Transv p a
  hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ s ∈ S, s ∈ H ∧ GGLinRefl s) ∧ H = Subgroup.closure S ∧
    ∀ s ∈ S, ∀ t ∈ S, Relation.ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ ¬ Commute u v) s t

@[expose] def A3NormalizerLeaf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (m : ℕ), 9 ≤ m → 3 ∣ m → ∀ (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (θ : (Fin m → ZMod p) →ₗ[ZMod p] V) (z : V), A3Frame p m θ z →
    ∀ a : V ≃ₗ[ZMod p] V, (∀ s, A3P p m θ z s → A3P p m θ z (a * s * a⁻¹)) → a z = z →
    A3P p m θ z a ∨ (θ (fun _ => 1) = 0 ∧ ∃ σ : Equiv.Perm (Fin m),
      ∀ u ∈ a3Aug p m, a (θ u) = -θ (fun i => u (σ.symm i)))

@[expose] def A3ReflFixLeaf : Prop :=
  A3NormalizerLeaf → ∀ (p : ℕ) [Fact p.Prime] (m : ℕ) (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (θ : (Fin m → ZMod p) →ₗ[ZMod p] V) (z : V)
    (H A : Subgroup (V ≃ₗ[ZMod p] V)),
    A3LinData p m V θ z H A → ∀ r ∈ A, GGLinRefl r → r z = z → A3P p m θ z r

@[expose] def A3PWeylLeaf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (m : ℕ), 9 ≤ m → 3 ∣ m → ∀ (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (θ : (Fin m → ZMod p) →ₗ[ZMod p] V) (z : V), A3Frame p m θ z →
    ∀ H : Subgroup (V ≃ₗ[ZMod p] V), (∀ a, a ∈ H ↔ A3P p m θ z a) → ZS.LinWeyl p H

@[expose] def A3ReflULeaf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (m : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    (θ : (Fin m → ZMod p) →ₗ[ZMod p] V) (z : V) (H A : Subgroup (V ≃ₗ[ZMod p] V)),
    A3LinData p m V θ z H A → θ (fun _ => 1) = z → ∀ r ∈ H, GGLinRefl r → r z = z

@[expose] def A3ReflM9Leaf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (m : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    (θ : (Fin m → ZMod p) →ₗ[ZMod p] V) (z : V) (H A : Subgroup (V ≃ₗ[ZMod p] V)),
    A3LinData p m V θ z H A → θ (fun _ => 1) = 0 → m = 9 → ∀ r ∈ H, GGLinRefl r →
    ggLinMove r ≤ (a3Aug p m).map θ → r z = z

@[expose] def A3StabCardLeaf : Prop :=
  A3NormalizerLeaf → ∀ (p : ℕ) [Fact p.Prime] (m : ℕ) (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (θ : (Fin m → ZMod p) →ₗ[ZMod p] V) (z : V)
    (H A : Subgroup (V ≃ₗ[ZMod p] V)),
    A3LinData p m V θ z H A →
    Nat.card {a : V ≃ₗ[ZMod p] V // a ∈ H ∧ a z = z} ≤ 2 * m.factorial

@[expose] def A3ClassReady (p : ℕ) [Fact p.Prime] (d : ℕ) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (H : Subgroup (V ≃ₗ[ZMod p] V)) : Prop :=
  ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod p) W) (R : Subgroup (W ≃ₗ[ZMod p] W)),
    Module.finrank (ZMod p) W = d ∧ ZS.AbsIrred p R ∧
    R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r} ∧
    Nat.card R ≤ 6 ^ d * d.factorial ∧ (ZS.LinWeyl p R → ZS.LinWeyl p H)

@[expose] def A3ReduceMLeaf : Prop :=
  A3StabCardLeaf → A3NormalizerLeaf → ∀ (p : ℕ) [Fact p.Prime] (m : ℕ) (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (θ : (Fin m → ZMod p) →ₗ[ZMod p] V) (z : V)
    (H A : Subgroup (V ≃ₗ[ZMod p] V)),
    A3LinData p m V θ z H A → θ (fun _ => 1) = 0 → 12 ≤ m →
    (∀ r ∈ H, GGLinRefl r → ggLinMove r ≤ (a3Aug p m).map θ) → A3ClassReady p (m - 2) H

@[expose] def A3ReduceVLeaf : Prop :=
  A3StabCardLeaf → A3ReflFixLeaf → A3NormalizerLeaf → ∀ (p : ℕ) [Fact p.Prime] (m : ℕ) (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (θ : (Fin m → ZMod p) →ₗ[ZMod p] V) (z : V)
    (H A : Subgroup (V ≃ₗ[ZMod p] V)),
    A3LinData p m V θ z H A → θ (fun _ => 1) = 0 → 12 ≤ m →
    (∃ r ∈ H, GGLinRefl r ∧ ¬ ggLinMove r ≤ (a3Aug p m).map θ) → (∃ a ∈ H, a z ≠ z) →
    A3ClassReady p (m - 1) H

@[expose] def A3LinSmallLeaf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (m : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    (θ : (Fin m → ZMod p) →ₗ[ZMod p] V) (z : V) (H A : Subgroup (V ≃ₗ[ZMod p] V)),
    A3LinData p m V θ z H A → θ (fun _ => 1) = 0 → m = 9 →
    (∃ r ∈ H, GGLinRefl r ∧ ¬ ggLinMove r ≤ (a3Aug p m).map θ) → (∃ a ∈ H, a z ≠ z) →
    ZS.LinWeyl p H

@[expose] def A3ModelAt {G : Type} [Group G] (p : ℕ) [Fact p.Prime] (Bs X : Subgroup G) (a : G) :
    Prop :=
  ∃ (m : ℕ) (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (θ : (Fin m → ZMod p) →ₗ[ZMod p] V) (ha : a ∈ Bs),
    p = 3 ∧ 9 ≤ m ∧ 3 ∣ m ∧ A3Frame p m θ (ι (Additive.ofMul (⟨a, ha⟩ : ↥Bs))) ∧
    ∀ g, g ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι) ↔
      A3P p m θ (ι (Additive.ofMul (⟨a, ha⟩ : ↥Bs))) g

@[expose] def A3LModelLeaf : Prop :=
  GGLabelRigidInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGResRowAt ggRowSUCorank3 p J L → A3ModelAt p Bs L x

@[expose] def A3LStabLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
    ∀ [Fact p.Prime], GGResRowAt ggRowSUCorank3 p J L → ∀ (hx : x ∈ Bs),
    ∀ ψ ∈ ggAutomizer ⊤ Bs, ψ ⟨x, hx⟩ = ⟨x, hx⟩ →
      ∀ φ ∈ ggAutomizer L Bs, ψ * φ * ψ⁻¹ ∈ ggAutomizer L Bs

@[expose] def A3KModelLeaf : Prop :=
  GGLabelRigidInput → GGLBalanceInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGResRowAt ggRowSUCorank3 p J K →
    A3ModelAt p Bs K y ∧ ∀ e ∈ Bs ⊓ Subgroup.centralizer (K : Set G), e ∈ Subgroup.zpowers y

@[expose] def A3KStabLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
    ∀ [Fact p.Prime], GGResRowAt ggRowSUCorank3 p J K → ∀ (hy : y ∈ Bs),
    (∀ e ∈ Bs ⊓ Subgroup.centralizer (K : Set G), e ∈ Subgroup.zpowers y) →
    ∀ ψ ∈ ggAutomizer ⊤ Bs, ψ ⟨y, hy⟩ = ⟨y, hy⟩ →
      ∀ φ ∈ ggAutomizer K Bs, ψ * φ * ψ⁻¹ ∈ ggAutomizer K Bs

@[expose] def A3AJLeaf : Prop :=
  GGResXDichotomyInput → GGTBJInputR → GGLabelRigidInput → GGLBalanceInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    (GGResRowAt ggRowSUCorank3 p J L → A3ModelAt p Bs L x) →
    (GGResRowAt ggRowSUCorank3 p J K → A3ModelAt p Bs K y) →
    (GGResRowAt ggRowSUCorank3 p J L ∨ GGResRowAt ggRowSUCorank3 p J K) →
    (∃ a ∈ ggAutomizer J Bs, ∃ b ∈ ggAutomizer J Bs, a * b ≠ b * a) ∧
      ggAutomizer J Bs ≤ ggAutomizer L Bs ⊓ ggAutomizer K Bs

end CFSG.StandardType.HdRo7A3
