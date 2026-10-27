module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure C2ReflNF (p : ℕ) [Fact p.Prime] {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (r : V ≃ₗ[ZMod p] V) (u : V) (φ : V →ₗ[ZMod p] ZMod p) : Prop where
  hr : r ∈ A
  hform : ∀ v, r v = v - φ v • u
  hφu : φ u = 2
  hφ0 : φ (b 0) = 1
  hu0 : b.coord 0 u ≠ 0

@[expose] def C2SuppTwoLeaf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (n : ℕ), 5 ≤ n → ∀ (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (s : V ≃ₗ[ZMod p] V),
    C2SP p b s → GGLinRefl s → ∀ v : V, v ≠ 0 → s v = -v →
      b.coord 0 v = 0 ∧ (Finset.univ.filter fun i => b.coord i v ≠ 0).card ≤ 2

@[expose] def C2ReflNormLeaf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (n : ℕ), 5 ≤ n → ∀ (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)),
    (∀ a, C2SP p b a → a ∈ A) → (∀ a ∈ A, a (b 0) = b 0 → C2SP p b a) →
    (∀ a ∈ A, ¬ C2Transv p a) →
    ∀ r ∈ A, GGLinRefl r → r (b 0) ≠ b 0 →
      ∃ (u : V) (φ : V →ₗ[ZMod p] ZMod p), C2ReflNF p b A r u φ

@[expose] def C2ReflCoefLeaf : Prop :=
  C2SuppTwoLeaf → ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (n : ℕ), 5 ≤ n → ∀ (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)),
    (∀ a, C2SP p b a → a ∈ A) → (∀ a ∈ A, a (b 0) = b 0 → C2SP p b a) →
    ∀ (r : V ≃ₗ[ZMod p] V) (u : V) (φ : V →ₗ[ZMod p] ZMod p), C2ReflNF p b A r u φ →
      ∃ c : ZMod p, ∀ i, i ≠ 0 → φ (b i) = c * b.coord i u

@[expose] def C2ReflSignLeaf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (n : ℕ), 5 ≤ n → ∀ (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)),
    (∀ a, C2SP p b a → a ∈ A) → (∀ a ∈ A, ¬ C2Transv p a) →
    ∀ (r : V ≃ₗ[ZMod p] V) (u : V) (φ : V →ₗ[ZMod p] ZMod p), C2ReflNF p b A r u φ →
      ∀ c : ZMod p, (∀ i, i ≠ 0 → φ (b i) = c * b.coord i u) →
      (c = 0 ∨ ∀ i, i ≠ 0 → b.coord i u = 0) → C2SignX p b r

@[expose] def C2ReflTrickLeaf : Prop :=
  C2SuppTwoLeaf → ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (n : ℕ), 5 ≤ n → ∀ (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)),
    (∀ a, C2SP p b a → a ∈ A) → (∀ a ∈ A, a (b 0) = b 0 → C2SP p b a) →
    ∀ (r : V ≃ₗ[ZMod p] V) (u : V) (φ : V →ₗ[ZMod p] ZMod p), C2ReflNF p b A r u φ →
      ∀ h : V ≃ₗ[ZMod p] V, C2SP p b h → φ (h u) = 1 → φ (h⁻¹ u) = 1 →
        (Finset.univ.filter fun i => b.coord i (h u - u) ≠ 0).card ≤ 2

@[expose] def C2ReflArithLeaf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (n : ℕ), 5 ≤ n → ∀ (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (r : V ≃ₗ[ZMod p] V) (u : V) (φ : V →ₗ[ZMod p] ZMod p),
    C2ReflNF p b A r u φ → ∀ c : ZMod p, (∀ i, i ≠ 0 → φ (b i) = c * b.coord i u) →
      b.coord 0 u + c * ((Finset.univ.filter fun i => i ≠ 0 ∧ b.coord i u ≠ 0).card : ZMod p) = 2

@[expose] def C2TableFlipLeaf : Prop :=
  C2ReflTrickLeaf → C2SuppTwoLeaf → ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (n : ℕ), 5 ≤ n → ∀ (V : Type)
    [AddCommGroup V] [Module (ZMod p) V] (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)),
    (∀ a, C2SP p b a → a ∈ A) → (∀ a ∈ A, a (b 0) = b 0 → C2SP p b a) →
    ∀ (r : V ≃ₗ[ZMod p] V) (u : V) (φ : V →ₗ[ZMod p] ZMod p), C2ReflNF p b A r u φ →
      ∀ c : ZMod p, (∀ i, i ≠ 0 → φ (b i) = c * b.coord i u) →
      b.coord 0 u + c * ((Finset.univ.filter fun i => i ≠ 0 ∧ b.coord i u ≠ 0).card : ZMod p) = 2 →
      ((c = 1 ∧ 5 ≤ (Finset.univ.filter fun i => i ≠ 0 ∧ b.coord i u ≠ 0).card) ∨
        (c = -1 ∧ 4 ≤ (Finset.univ.filter fun i => i ≠ 0 ∧ b.coord i u ≠ 0).card)) → False

@[expose] def C2TableSmallLeaf : Prop :=
  C2ReflTrickLeaf → C2SuppTwoLeaf → ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (n : ℕ), 5 ≤ n → ∀ (V : Type)
    [AddCommGroup V] [Module (ZMod p) V] (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)),
    (∀ a, C2SP p b a → a ∈ A) → (∀ a ∈ A, a (b 0) = b 0 → C2SP p b a) →
    ∀ (r : V ≃ₗ[ZMod p] V) (u : V) (φ : V →ₗ[ZMod p] ZMod p), C2ReflNF p b A r u φ →
      ∀ c : ZMod p, (∀ i, i ≠ 0 → φ (b i) = c * b.coord i u) → c ≠ 0 →
      (∃ i, i ≠ 0 ∧ b.coord i u ≠ 0) →
      b.coord 0 u + c * ((Finset.univ.filter fun i => i ≠ 0 ∧ b.coord i u ≠ 0).card : ZMod p) = 2 →
      ¬ ((c = 1 ∧ 5 ≤ (Finset.univ.filter fun i => i ≠ 0 ∧ b.coord i u ≠ 0).card) ∨
        (c = -1 ∧ 4 ≤ (Finset.univ.filter fun i => i ≠ 0 ∧ b.coord i u ≠ 0).card)) → C2Swap p b r

end CFSG.StandardType.HdRo7C
