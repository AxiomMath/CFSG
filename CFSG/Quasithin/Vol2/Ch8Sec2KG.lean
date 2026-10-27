module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def KG82CoverL34 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    Nat.card ↥(Subgroup.center K) = 2 → IsPSL 3 2 2 (K ⧸ Subgroup.center K) →
      ∀ P : Subgroup K, Subgroup.center K ≤ P → Nat.card ↥P = 2 * 960 →
        ⁅pCoreOf 2 P, P⁆ = pCoreOf 2 P

@[expose] def KG82CoverM22 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    Nat.card ↥(Subgroup.center K) = 2 → IsSporadic .M22 (K ⧸ Subgroup.center K) →
      ∀ X : Subgroup K, Subgroup.center K ≤ X →
        IsPSL 3 2 2 (↥X ⧸ (Subgroup.center K).subgroupOf X) →
          ∀ P : Subgroup K, Subgroup.center K ≤ P → P ≤ X → Nat.card ↥P = 2 * 960 →
            ⁅pCoreOf 2 P, P⁆ = pCoreOf 2 P

@[expose] def KG82HatM22Twelve : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    Nat.card ↥(Subgroup.center K) = 3 → IsSporadic .M22 (K ⧸ Subgroup.center K) →
      ∀ (W : Type) [CommGroup W] [Finite W], Nat.card W = 2 ^ 12 → (∀ w : W, w ^ 2 = 1) →
        ∀ ρ : K →* MulAut W, Function.Injective ρ →
          Subgroup.centralizer (ρ.range : Set (MulAut W)) = (Subgroup.center K).map ρ

@[expose] def KG82HatM22Out : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    Nat.card ↥(Subgroup.center K) = 3 → IsSporadic .M22 (K ⧸ Subgroup.center K) →
      ∀ α : MulAut K, (∀ k : K, α ≠ MulAut.conj k) → ∀ z ∈ Subgroup.center K, α z = z⁻¹

end CFSG.Quasithin.H13
