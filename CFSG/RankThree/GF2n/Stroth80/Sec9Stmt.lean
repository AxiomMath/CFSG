module

public import CFSG.RankThree.GF2n.Stroth80.Sec9Defs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec7Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Stroth91aStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → OmegaPlusNat hc t 2

@[expose] def Stroth91bStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ r : G, Sec7A hc t r → ∀ (V W : Subgroup G),
      V = Vt M (LB M Q B) B Z t → W = Wt Q V →
      IsDirectSumSec W V ((QB (conjSubgroup r B) ⊓ W) ⊔ V) ((QB B ⊓ W) ⊔ V) ∧
      ∀ s ∈ hc.CN t, ∀ x ∈ W, ⁅s, x⁆ ∈ V

@[expose] def Stroth91cStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ (R V W : Subgroup G), R = Rt M (LB M Q B) t →
      V = Vt M (LB M Q B) B Z t → W = Wt Q V → IsChiIso Q R W V Z t

@[expose] def Stroth91Statement : Prop :=
  Stroth91aStatement ∧ Stroth91bStatement ∧ Stroth91cStatement

@[expose] def Stroth92Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ (V W : Subgroup G), V = Vt M (LB M Q B) B Z t → W = Wt Q V →
    ∀ x ∈ LB M Q B, x ∉ hc.CN t → (∀ w ∈ W, ⁅x, w⁆ ∈ V) →
      (∃ Y : Subgroup G, IsDirectProdQuot (Rt M (LB M Q B) t) (Sec9R0 hc t x) Y Q ∧
        QuotSat Y Q (IsSLModel 2 (Nat.card Z))) ∧
      ∀ a ∈ Sec9R0 hc t x, ∀ w ∈ W, ⁅a, w⁆ ∈ V

@[expose] def Stroth93Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
      ¬ StronglyClosedMod M Z0 (LB M Q B)

@[expose] def Stroth94Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
      ¬ StronglyClosedMod M Z0 (LB M Q B ⊓ hc.CN t)

@[expose] def Sec9AExistsStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∃ r : G, Sec7A hc t r

@[expose] def Sec9NCommStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ⁅hc.CN t, hc.CN t⁆ ≤ LB M Q B

@[expose] def Sec9NGeFiveStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → 5 ≤ n

@[expose] def Step91OrderQBStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ (V W : Subgroup G), V = Vt M (LB M Q B) B Z t → W = Wt Q V →
      Nat.card ↥(Q ⊓ QB B ⊓ W) * Nat.card Z = Nat.card ↥(Q ⊓ QB B)

@[expose] def Step91OrderVQBStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ V : Subgroup G, V = Vt M (LB M Q B) B Z t →
      Nat.card ↥(V ⊓ QB B) = Nat.card Z ^ 4

@[expose] def Step91InterStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ r : G, Sec7A hc t r → ∀ (V W : Subgroup G),
      V = Vt M (LB M Q B) B Z t → W = Wt Q V →
      Nat.card ↥(QB (conjSubgroup r B) ⊓ QB B ⊓ W) ≤ Nat.card Z ^ 3

@[expose] def Step91MixedCommStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ r : G, Sec7A hc t r → ∀ (V W : Subgroup G),
      V = Vt M (LB M Q B) B Z t → W = Wt Q V →
      (∀ s ∈ LB M Q B ⊓ hc.CN t, ∀ x ∈ QB (conjSubgroup r B) ⊓ W, ⁅s, x⁆ ∈ V) ∧
      (∀ s ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t, ∀ x ∈ QB B ⊓ W, ⁅s, x⁆ ∈ V)

@[expose] def Step92NontrivStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ (V W : Subgroup G), V = Vt M (LB M Q B) B Z t → W = Wt Q V →
      ∃ ρ ∈ Rt M (LB M Q B) t, ∃ w ∈ W, ⁅ρ, w⁆ ∉ V

@[expose] def Step92QuotStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ x ∈ LB M Q B, x ∉ hc.CN t → Sec9R0 hc t x < Rt M (LB M Q B) t →
      QuotSat (Sec9R0 hc t x) (hc.CN t) (IsSLModel 2 (Nat.card Z))

@[expose] def Step92SplitStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ (V W : Subgroup G), V = Vt M (LB M Q B) B Z t → W = Wt Q V →
    ∀ x ∈ LB M Q B, x ∉ hc.CN t → (∀ w ∈ W, ⁅x, w⁆ ∈ V) →
      Sec9R0 hc t x < Rt M (LB M Q B) t →
      QuotSat (Sec9R0 hc t x) (hc.CN t) (IsSLModel 2 (Nat.card Z)) →
      ∃ Y : Subgroup G, IsDirectProdQuot (Rt M (LB M Q B) t) (Sec9R0 hc t x) Y Q ∧
        QuotSat Y Q (IsSLModel 2 (Nat.card Z))

@[expose] def Step93OneStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ r : G, Sec7A hc t r →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    StronglyClosedMod M Z0 (LB M Q B) →
    ∀ m ∈ M, conjSubgroup m B ⊔ Z ≤ Vt M (LB M Q B) B Z t →
      ∃ ρ ∈ Rt M (LB M Q B) t, conjSubgroup m B ⊔ Z = conjSubgroup ρ B ⊔ Z

@[expose] def Step93VanishStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ r : G, Sec7A hc t r →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    StronglyClosedMod M Z0 (LB M Q B) → ∀ s z : G, Sec9T1 M Q Z0 s z →
      ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅z * s * z⁻¹, v⁆ ∈ Z

@[expose] def Step93TIStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ r : G, Sec7A hc t r →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    StronglyClosedMod M Z0 (LB M Q B) → ∀ h ∈ M,
      LB M Q B ⊓ conjSubgroup h (LB M Q B) ≠ Q →
      Z0 ⊓ (LB M Q B ⊓ conjSubgroup h (LB M Q B)) ≠ Q

@[expose] def Step93FourStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ r : G, Sec7A hc t r →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    StronglyClosedMod M Z0 (LB M Q B) → ∀ s z : G, Sec9T1 M Q Z0 s z →
      (∀ m ∈ M, conjSubgroup m B ⊔ Z ≤ Vt M (LB M Q B) B Z t →
        ∃ ρ ∈ Rt M (LB M Q B) t, conjSubgroup m B ⊔ Z = conjSubgroup ρ B ⊔ Z) →
      (∀ v ∈ Vt M (LB M Q B) B Z t, ⁅z * s * z⁻¹, v⁆ ∈ Z) →
      (∀ h ∈ M, LB M Q B ⊓ conjSubgroup h (LB M Q B) ≠ Q →
        Z0 ⊓ (LB M Q B ⊓ conjSubgroup h (LB M Q B)) ≠ Q) →
      Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t) = Z

@[expose] def Step93EndStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ r : G, Sec7A hc t r →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    StronglyClosedMod M Z0 (LB M Q B) → ∀ s z : G, Sec9T1 M Q Z0 s z →
      Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t) = Z → False

@[expose] def Step94ConjVStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ (V W : Subgroup G), V = Vt M (LB M Q B) B Z t → W = Wt Q V →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ s ∈ Z0, ∀ x ∈ LB M Q B, x ∉ hc.CN t → ConjMod M Q s x → ∀ w ∈ W, ⁅x, w⁆ ∈ V

@[expose] def Step94NSixStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    StronglyClosedMod M Z0 (LB M Q B ⊓ hc.CN t) →
    ∀ s ∈ Z0, ∀ x ∈ LB M Q B, x ∉ hc.CN t → ConjMod M Q s x →
    (∃ Y : Subgroup G, IsDirectProdQuot (Rt M (LB M Q B) t) (Sec9R0 hc t x) Y Q ∧
        QuotSat Y Q (IsSLModel 2 (Nat.card Z))) → n = 6

@[expose] def Step94EndStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    StronglyClosedMod M Z0 (LB M Q B ⊓ hc.CN t) →
    ∀ s ∈ Z0, ∀ x ∈ LB M Q B, x ∉ hc.CN t → ConjMod M Q s x →
    (∃ Y : Subgroup G, IsDirectProdQuot (Rt M (LB M Q B) t) (Sec9R0 hc t x) Y Q ∧
        QuotSat Y Q (IsSLModel 2 (Nat.card Z))) → n = 6 → False

end CFSG.RankThree.GF2n.Stroth80
