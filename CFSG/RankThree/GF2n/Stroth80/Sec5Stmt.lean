module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

@[expose] def Vone (Q B C V : Subgroup G) : Subgroup G := ((Q ⊓ QB B) ⊔ V) ⊓ ((Q ⊓ QB C) ⊔ V)

@[expose] def Stroth51Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → (SpNat hc t ∨ OmegaNat hc t) →
    ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
    ∀ (C L L' N R : Subgroup G), C = conjSubgroup r B → L = LB M Q B → L' = LB M Q C →
      N = hc.CN t → R = Rt M L t →
      (∀ x ∈ N, ∃ a ∈ L ⊓ N, ∃ b ∈ L' ⊓ N, x = a * b) ∧
      Nat.card ↥(L ⊓ L') = Nat.card Q * Nat.card Z ∧
      (∀ s ∈ R, ∀ x ∈ L ⊓ L', ⁅s, x⁆ ∈ Q) ∧
      IsOppDecomp N (L ⊓ L') L L' (L ⊓ N) (L' ⊓ N)

@[expose] def Stroth52aStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → OmegaNat hc t →
    ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
    ∀ (C N V W : Subgroup G), C = conjSubgroup r B → N = hc.CN t → V = Vt M (LB M Q B) B Z t →
      W = Wt Q V →
      (∀ x ∈ W, ∃ a ∈ QB B ⊓ W, ∃ b ∈ QB C ⊓ W, x = a * b) ∧ (∀ s ∈ N, ∀ x ∈ W, ⁅s, x⁆ ∈ V)

@[expose] def Stroth52bStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → OmegaNat hc t →
    ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
    ∀ (C L L' V W : Subgroup G), C = conjSubgroup r B → L = LB M Q B → L' = LB M Q C →
      V = Vt M L B Z t → W = Wt Q V →
      IsOppDecomp W V L L' ((QB B ⊓ W) ⊔ V) ((QB C ⊓ W) ⊔ V)

@[expose] def Stroth52cStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → OmegaNat hc t →
    ∀ (R V W : Subgroup G), R = Rt M (LB M Q B) t → V = Vt M (LB M Q B) B Z t → W = Wt Q V →
      IsChiIso Q R W V Z t

@[expose] def Stroth53aStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → SpNat hc t →
    ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
    ∀ (C V W V₁ W₁ : Subgroup G), C = conjSubgroup r B → V = Vt M (LB M Q B) B Z t →
      W = Wt Q V → V₁ = Vone Q B C V → W₁ = Wt Q V₁ →
      Nat.card ↥V₁ = Nat.card V * Nat.card Z ∧ Nat.card W = Nat.card W₁ * Nat.card Z ∧ Odd n

@[expose] def Stroth53bStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → SpNat hc t →
    ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
    ∀ (C N V W₁ V₁ : Subgroup G), C = conjSubgroup r B → N = hc.CN t →
      V = Vt M (LB M Q B) B Z t → V₁ = Vone Q B C V → W₁ = Wt Q V₁ →
      (∀ x ∈ W₁, ∃ a ∈ QB B ⊓ W₁, ∃ b ∈ QB C ⊓ W₁, x = a * b) ∧
      (∀ s ∈ N, ∀ x ∈ W₁, ⁅s, x⁆ ∈ V₁)

@[expose] def Stroth53cStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → SpNat hc t →
    ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
    ∀ (C L L' V W₁ V₁ : Subgroup G), C = conjSubgroup r B → L = LB M Q B → L' = LB M Q C →
      V = Vt M L B Z t → V₁ = Vone Q B C V → W₁ = Wt Q V₁ →
      IsOppDecomp W₁ V₁ L L' ((QB B ⊓ W₁) ⊔ V₁) ((QB C ⊓ W₁) ⊔ V₁)

@[expose] def Stroth53dStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → SpNat hc t →
    ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
    ∀ (C N R V W₁ V₁ : Subgroup G), C = conjSubgroup r B → N = hc.CN t →
      R = Rt M (LB M Q B) t → V = Vt M (LB M Q B) B Z t → V₁ = Vone Q B C V → W₁ = Wt Q V₁ →
      (∀ s ∈ N, ∀ x ∈ V₁, ⁅s, x⁆ ∈ Z) ∧ (∀ s ∈ N, ∀ x ∈ Q, ⁅s, x⁆ ∈ W₁) ∧
      IsIndecSec R V₁ Z

@[expose] def Stroth53eStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → SpNat hc t →
    ∀ (R V W : Subgroup G), R = Rt M (LB M Q B) t → V = Vt M (LB M Q B) B Z t → W = Wt Q V →
      IsChiIso Q R W V Z t

@[expose] def Stroth53Statement : Prop :=
  Stroth53aStatement ∧ Stroth53bStatement ∧ Stroth53cStatement ∧ Stroth53dStatement ∧
    Stroth53eStatement

@[expose] def Stroth54Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → SpNat hc t → Nat.card ↥(hc.CN t) ≠ Nat.card Q * Nat.card Z

@[expose] def Stroth57Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → SLNat hc t → (∃ g : G, ∃ b ∈ B, g * t * g⁻¹ = b) →
      B ≤ QB (Subgroup.zpowers t) →
        Vt M (LB M Q B) B Z t ≤ (Q ⊓ QB (Subgroup.zpowers t)) ⊔ Z

@[expose] def Stroth310ChiStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → (SpNat hc t ∨ OmegaNat hc t) →
      Vt M (LB M Q B) B Z t = Ut Q Z t ∧ Wt Q (Vt M (LB M Q B) B Z t) = Q1 hc t

@[expose] def Stroth310NotQBStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → (SpNat hc t ∨ OmegaNat hc t) → ¬ Vt M (LB M Q B) B Z t ≤ QB B

@[expose] def Stroth310RootStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → (SpNat hc t ∨ OmegaNat hc t) →
    ∀ (V : Subgroup G), V = Vt M (LB M Q B) B Z t →
    ∀ r ∈ Rt M (LB M Q B) t,
      (r ∈ LB M Q B ⊔ hc.CN t ↔
        ((∀ b ∈ B, ⁅r, b⁆ ∈ Z) ∧ (∀ v ∈ V ⊓ QB B, ⁅r, v⁆ ∈ B ⊔ Z) ∧
          (∀ v ∈ V, ⁅r, v⁆ ∈ V ⊓ QB B)))

end CFSG.RankThree.GF2n.Stroth80
