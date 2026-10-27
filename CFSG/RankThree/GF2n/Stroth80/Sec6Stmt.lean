module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Stroth6LBStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Stroth6Hyp hc n t →
    (∀ m : ℕ, 2 ≤ m → (SLMNat hc t m ∨ (m = 2 ∧ SpMNat hc t 1)) →
      Nat.card ↥(LB M Q B) = Nat.card Q * Nat.card Z ^ m) ∧
    (∀ m : ℕ, 2 ≤ m → (OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m) →
      Nat.card ↥(LB M Q B) = Nat.card Q * Nat.card Z ^ (2 * m - 1))

@[expose] def Stroth6SLDimStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → ∀ m : ℕ, 2 ≤ m → (SLMNat hc t m ∨ (m = 2 ∧ SpMNat hc t 1)) → 2 * m ≤ n

@[expose] def Stroth61Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Stroth6Hyp hc n t → ¬ SLlike hc t

@[expose] def Stroth62Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Stroth6Hyp hc n t → (OmegaPlusNat hc t 2 ∨ OmegaMinusNat hc t 2) → n = 4

@[expose] def Stroth63aStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Stroth6Hyp hc n t → ∀ m : ℕ, 3 ≤ m → (OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m) →
      n = 2 * m

@[expose] def Stroth63bStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Stroth6Hyp hc n t → ∀ m : ℕ, 3 ≤ m → (OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m) →
    StronglyClosedMod M (hc.CN t) (LB M Q B)

@[expose] def Stroth64Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Stroth6Hyp hc n t → ∀ m : ℕ, 3 ≤ m → (OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m) →
    QuotSat (Lgen M (hc.CN t)) Q (IsSLModel 2 (Nat.card Z))

@[expose] def Stroth65Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Stroth6Hyp hc n t →
    (n = 4 ∧ (QuotSat (Rt M (LB M Q B) t) (hc.CN t) (IsOmegaPlus 2 (Nat.card Z)) ∨
      QuotSat (Rt M (LB M Q B) t) (hc.CN t) (IsOmegaMinus 2 (Nat.card Z)))) ∨
    ∃ m : ℕ, 3 ≤ m ∧ n = 2 * m ∧ ∃ X C : Subgroup G,
      Q ≤ X ∧ X ≤ Rt M (LB M Q B) t ∧ hc.CN t ⊔ X = Rt M (LB M Q B) t ∧ hc.CN t ⊓ X = Q ∧
      (∀ a ∈ hc.CN t, ∀ x ∈ X, ⁅a, x⁆ ∈ Q) ∧ (X.subgroupOf M).Normal ∧
      ((OmegaPlusNat hc t m ∧ QuotSat X Q (IsOmegaPlus m (Nat.card Z))) ∨
        (OmegaMinusNat hc t m ∧ QuotSat X Q (IsOmegaMinus m (Nat.card Z)))) ∧
      (∀ h, h ∈ C ↔ h ∈ H0 M Z ∧ ∀ x ∈ X, ⁅h, x⁆ ∈ Q) ∧ Lgen M (hc.CN t) = C ∧ C ⊓ X = Q ∧
      QuotSat C Q (IsSLModel 2 (Nat.card Z))

@[expose] def Stroth65XStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Stroth6Hyp hc n t → ∀ m : ℕ, 3 ≤ m → n = 2 * m →
    (OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m) → ∃ X C : Subgroup G,
      Q ≤ X ∧ X ≤ Rt M (LB M Q B) t ∧ hc.CN t ⊔ X = Rt M (LB M Q B) t ∧ hc.CN t ⊓ X = Q ∧
      (∀ a ∈ hc.CN t, ∀ x ∈ X, ⁅a, x⁆ ∈ Q) ∧ (X.subgroupOf M).Normal ∧
      ((OmegaPlusNat hc t m ∧ QuotSat X Q (IsOmegaPlus m (Nat.card Z))) ∨
        (OmegaMinusNat hc t m ∧ QuotSat X Q (IsOmegaMinus m (Nat.card Z)))) ∧
      (∀ h, h ∈ C ↔ h ∈ H0 M Z ∧ ∀ x ∈ X, ⁅h, x⁆ ∈ Q) ∧ Lgen M (hc.CN t) = C ∧ C ⊓ X = Q ∧
      QuotSat C Q (IsSLModel 2 (Nat.card Z))

end CFSG.RankThree.GF2n.Stroth80
