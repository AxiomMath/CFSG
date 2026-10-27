module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin

@[expose] def SchurMult2A7 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsAlt 7 (K ⧸ Subgroup.center K) →
      Nat.card ↥(Subgroup.center K) ∣ 2

@[expose] def SchurMult2L2Odd : Prop :=
  ∀ p f : ℕ, p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsPSL 2 p f (K ⧸ Subgroup.center K) →
      Nat.card ↥(Subgroup.center K) ∣ 2

@[expose] def SchurMult2L35 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsPSL 3 5 1 (K ⧸ Subgroup.center K) →
      Subgroup.center K = ⊥

@[expose] def SchurMult2U35 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsPSU 3 5 1 (K ⧸ Subgroup.center K) →
      Subgroup.center K = ⊥

@[expose] def SchurMult2J1 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsSporadic .J1 (K ⧸ Subgroup.center K) →
      Subgroup.center K = ⊥

@[expose] def SchurMult2J2 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsSporadic .J2 (K ⧸ Subgroup.center K) →
      Nat.card ↥(Subgroup.center K) ∣ 2

@[expose] def SchurMult2HS : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsSporadic .HS (K ⧸ Subgroup.center K) →
      Nat.card ↥(Subgroup.center K) ∣ 2

@[expose] def SchurMult2Ru : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsSporadic .Ru (K ⧸ Subgroup.center K) →
      Nat.card ↥(Subgroup.center K) ∣ 2

@[expose] def SchurMult2L34Rank : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → IsPSL 3 2 2 (K ⧸ Subgroup.center K) →
      ∀ E : Subgroup K, E ≤ Subgroup.center K → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≤ 4

end CFSG.Quasithin
