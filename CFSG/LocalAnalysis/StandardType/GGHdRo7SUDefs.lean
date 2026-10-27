module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs
public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def SUPerm (p : ℕ) {V : Type} [AddCommGroup V] [Module (ZMod p) V] {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod p) V) (a : V ≃ₗ[ZMod p] V) : Prop :=
  ∃ σ : Equiv.Perm (Fin m), ∀ i, a (b i) = b (σ i)

@[expose] noncomputable def SUOnes (p : ℕ) {V : Type} [AddCommGroup V] [Module (ZMod p) V] {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod p) V) : V := ∑ i, b i

@[expose] noncomputable def SUAug (p : ℕ) {V : Type} [AddCommGroup V] [Module (ZMod p) V] {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod p) V) : Submodule (ZMod p) V :=
  LinearMap.ker (∑ i, b.coord i)

structure SULinData (p : ℕ) [Fact p.Prime] (m : ℕ) (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin m) (ZMod p) V)
    (H A : Subgroup (V ≃ₗ[ZMod p] V)) : Prop where
  hp : p = 3
  hm : 7 ≤ m
  h3 : ¬ 3 ∣ m
  hPH : ∀ a, SUPerm p b a → a ∈ H
  hHA : H ≤ A
  hStab : ∀ a ∈ A, a (SUOnes p b) = SUOnes p b →
    ∀ s, SUPerm p b s → SUPerm p b (a * s * a⁻¹)
  hNoT : ∀ a ∈ A, ¬ C2Transv p a
  hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ s ∈ S, s ∈ H ∧ GGLinRefl s) ∧ H = Subgroup.closure S ∧
    ∀ s ∈ S, ∀ t ∈ S, Relation.ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ ¬ Commute u v) s t

@[expose] def SUClassReady (p : ℕ) [Fact p.Prime] (m : ℕ) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (H : Subgroup (V ≃ₗ[ZMod p] V)) : Prop :=
  ∃ (d : ℕ) (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod p) W)
    (R : Subgroup (W ≃ₗ[ZMod p] W)),
    (d = m - 1 ∨ d = m) ∧ Module.finrank (ZMod p) W = d ∧ ZS.AbsIrred p R ∧
    R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r} ∧
    Nat.card R ≤ 2 * 3 ^ d * (d + 1).factorial ∧ (ZS.LinWeyl p R → ZS.LinWeyl p H)

@[expose] def SUNormalizerLeaf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (m : ℕ), 7 ≤ m → ¬ 3 ∣ m → ∀ (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin m) (ZMod p) V) (a : V ≃ₗ[ZMod p] V),
    (∀ s, SUPerm p b s → SUPerm p b (a * s * a⁻¹)) → a (SUOnes p b) = SUOnes p b →
    SUPerm p b a ∨ ∃ σ : Equiv.Perm (Fin m),
      ∀ i, a (b i) = -b (σ i) + (2 / (m : ZMod p)) • SUOnes p b

@[expose] def SUClassLargeLeaf : Prop :=
  GGReflClassLargeInput' → ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (d : ℕ), 9 ≤ d →
    ∀ (W : Type) [AddCommGroup W] [Module (ZMod p) W], Module.finrank (ZMod p) W = d →
    ∀ R : Subgroup (W ≃ₗ[ZMod p] W), ZS.AbsIrred p R →
    R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r} →
    Nat.card R ≤ 2 * 3 ^ d * (d + 1).factorial → ZS.LinWeyl p R

@[expose] def SULinSmallLeaf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (m : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin m) (ZMod p) V) (H A : Subgroup (V ≃ₗ[ZMod p] V)),
    SULinData p m V b H A → (m = 7 ∨ m = 8) → ZS.LinWeyl p H

@[expose] def SUGraphLeaf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    (AL AK J : Subgroup (V ≃ₗ[ZMod p] V)) (SL SK : Set (V ≃ₗ[ZMod p] V)),
    (∀ s ∈ SL, s ∈ AL ∧ GGLinRefl s) → AL = Subgroup.closure SL →
    (∀ s ∈ SL, ∀ t ∈ SL,
      Relation.ReflTransGen (fun u v => u ∈ SL ∧ v ∈ SL ∧ ¬ Commute u v) s t) →
    (∀ s ∈ SK, s ∈ AK ∧ GGLinRefl s) → AK = Subgroup.closure SK →
    (∀ s ∈ SK, ∀ t ∈ SK,
      Relation.ReflTransGen (fun u v => u ∈ SK ∧ v ∈ SK ∧ ¬ Commute u v) s t) →
    J ≤ AL → J ≤ AK → (∃ a ∈ J, ∃ b ∈ J, a * b ≠ b * a) →
    ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ s ∈ S, s ∈ AL ⊔ AK ∧ GGLinRefl s) ∧ AL ⊔ AK = Subgroup.closure S ∧
      ∀ s ∈ S, ∀ t ∈ S, Relation.ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ ¬ Commute u v) s t

@[expose] def SUModelAt {G : Type} [Group G] (p : ℕ) [Fact p.Prime] (Bs X : Subgroup G) (a : G) : Prop :=
  ∃ (m : ℕ) (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (b : Module.Basis (Fin m) (ZMod p) V) (ha : a ∈ Bs),
    p = 3 ∧ 7 ≤ m ∧ ¬ 3 ∣ m ∧ ι (Additive.ofMul (⟨a, ha⟩ : ↥Bs)) = SUOnes p b ∧
    ∀ g, g ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι) ↔ SUPerm p b g

@[expose] def SUKStabLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
    ∀ [Fact p.Prime], GGResRowAt ggRowSUCorank2 p J K →
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
      (b : Module.Basis (Fin m) (ZMod p) V) (hy : y ∈ Bs), p = 3 → 7 ≤ m → ¬ 3 ∣ m →
      ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) = SUOnes p b →
      (∀ g, g ∈ (ggAutomizer K Bs).map (ggLin (p := p) ι) ↔ SUPerm p b g) →
      ∀ a ∈ (ggAutomizer ⊤ Bs).map (ggLin (p := p) ι), a (SUOnes p b) = SUOnes p b →
        ∀ s, SUPerm p b s → SUPerm p b (a * s * a⁻¹)

@[expose] def SUAJLeaf : Prop :=
  GGResXDichotomyInput → GGTBJInputR → GGLabelRigidInput → GGLBalanceInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    (GGResRowAt ggRowSUCorank2 p J L → SUModelAt p Bs L x) →
    (GGResRowAt ggRowSUCorank2 p J K → SUModelAt p Bs K y) →
    (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K) →
    (∃ a ∈ ggAutomizer J Bs, ∃ b ∈ ggAutomizer J Bs, a * b ≠ b * a) ∧
      ggAutomizer J Bs ≤ ggAutomizer L Bs ⊓ ggAutomizer K Bs

end CFSG.StandardType.HdRo7SU
