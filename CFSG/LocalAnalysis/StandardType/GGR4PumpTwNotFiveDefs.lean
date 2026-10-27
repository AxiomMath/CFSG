module

public import CFSG.LocalAnalysis.StandardType.GGR4PumpDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGPumpTwNotFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → p = 3 → Nat.card Bs = 3 ^ 5 → ∀ f : ℕ,
    ((3 ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.twA, 5, f⟩ (J ⧸ Subgroup.center J)) ∨
      (3 ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.A, 5, f⟩ (J ⧸ Subgroup.center J)) ∨
      GGHasLabel ⟨.twD, 4, f⟩ (J ⧸ Subgroup.center J)) →
    ∀ z ∈ D, z ≠ 1 → ∀ X : Subgroup G,
      LargeEvenPComponent p (Subgroup.centralizer ({z} : Set G)) X → J ≤ X →
      LargeEvenPComponent p (X ⊓ Subgroup.centralizer ({x} : Set G)) J → GGInnerDiagOn Bs X →
      3 ≤ Nat.log p (Nat.card (Bs ⊓ J : Subgroup G)) →
      ¬ (⁅X, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p X →
      ¬ 5 ∣ Nat.card (ggAutomizer X Bs)

@[expose] def GGR4NotFiveAtLine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J → Nat.card Bs = 3 ^ 5 → GGR4JLabel (J ⧸ Subgroup.center J) →
    ∀ z ∈ D, z ≠ 1 → ∀ X : Subgroup G,
      LargeEvenPComponent 3 (Subgroup.centralizer ({z} : Set G)) X → J ≤ X →
      LargeEvenPComponent 3 (X ⊓ Subgroup.centralizer ({x} : Set G)) J → GGInnerDiagOn Bs X →
      3 ≤ Nat.log 3 (Nat.card (Bs ⊓ J : Subgroup G)) →
      ¬ (⁅X, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf 3 X →
      ¬ 5 ∣ Nat.card (ggAutomizer X Bs)

end CFSG.StandardType
