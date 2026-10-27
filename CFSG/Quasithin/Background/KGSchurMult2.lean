module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin

@[expose] def SchurMult2M22 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsSporadic .M22 (K ⧸ Subgroup.center K) →
      IsCyclic ↥(Subgroup.center K) ∧ Nat.card ↥(Subgroup.center K) ∣ 4

@[expose] def SchurMult2M23 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsSporadic .M23 (K ⧸ Subgroup.center K) →
      Subgroup.center K = ⊥

@[expose] def SchurMult2M24 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsSporadic .M24 (K ⧸ Subgroup.center K) →
      Subgroup.center K = ⊥

@[expose] def SchurMult2J4 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsSporadic .J4 (K ⧸ Subgroup.center K) →
      Subgroup.center K = ⊥

@[expose] def SchurMult2He : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsSporadic .He (K ⧸ Subgroup.center K) →
      Subgroup.center K = ⊥

@[expose] def SchurMult2L32 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsPSL 3 2 1 (K ⧸ Subgroup.center K) →
      Nat.card ↥(Subgroup.center K) ∣ 2

@[expose] def SchurMult2L34 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsPSL 3 2 2 (K ⧸ Subgroup.center K) →
      Nat.card ↥(Subgroup.center K) ∣ 16

@[expose] def SchurMult2L3 : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsPSL 3 2 n (K ⧸ Subgroup.center K) →
      Subgroup.center K = ⊥

@[expose] def SchurMult2L42 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsPSL 4 2 1 (K ⧸ Subgroup.center K) →
      Nat.card ↥(Subgroup.center K) ∣ 2

@[expose] def SchurMult2L52 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsPSL 5 2 1 (K ⧸ Subgroup.center K) →
      Subgroup.center K = ⊥

@[expose] def SchurMult2Sp4 : Prop :=
  ∀ n : ℕ, ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsPSp4 2 n (K ⧸ Subgroup.center K) →
      Subgroup.center K = ⊥

@[expose] def SchurMult2G24 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsG2 2 2 (K ⧸ Subgroup.center K) →
      Nat.card ↥(Subgroup.center K) ∣ 2

@[expose] def SchurMult2G2 : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsG2 2 n (K ⧸ Subgroup.center K) →
      Subgroup.center K = ⊥

@[expose] def SchurMult2D4 : Prop :=
  ∀ n : ℕ, ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → Is3D4 2 n (K ⧸ Subgroup.center K) →
      Subgroup.center K = ⊥

@[expose] def SchurMult2F4 : Prop :=
  ∀ n : ℕ, ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → Is2F4 n (K ⧸ Subgroup.center K) →
      Subgroup.center K = ⊥

@[expose] def SchurMult2U4 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsPSU 4 2 n (K ⧸ Subgroup.center K) →
      Subgroup.center K = ⊥

@[expose] def SchurMult2U5 : Prop :=
  ∀ n : ℕ, ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsPSU 5 2 n (K ⧸ Subgroup.center K) →
      Subgroup.center K = ⊥

structure SchurMultTwoTable : Prop where
  m22 : SchurMult2M22
  m23 : SchurMult2M23
  m24 : SchurMult2M24
  j4 : SchurMult2J4
  he : SchurMult2He
  l32 : SchurMult2L32
  l34 : SchurMult2L34
  l3 : SchurMult2L3
  l42 : SchurMult2L42
  l52 : SchurMult2L52
  sp4 : SchurMult2Sp4
  g24 : SchurMult2G24
  g2 : SchurMult2G2
  d4 : SchurMult2D4
  f4 : SchurMult2F4
  u4 : SchurMult2U4
  u5 : SchurMult2U5

end CFSG.Quasithin
