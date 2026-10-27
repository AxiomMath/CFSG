
module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def A129One : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (G : Type) [Group G] [Finite G] (P H : Subgroup G),
    P.Normal → IsPGroup p ↥P → Subgroup.closure {x : G | x ∈ P ∧ x ^ p = 1} = P →
    ClassLeTwo P → CFSG.Open.pRank p P = 2 → ⁅H, H⁆ = H → ⁅P, H⁆ ≠ ⊥ →
    ∃ (C : Subgroup ↥H) (_ : C.Normal),
      (∀ h : ↥H, h ∈ C ↔ ActsTriviallyOnFrattiniQuotient P (h : G)) ∧
      (IsSL2 p (↥H ⧸ C) ∨ ((p % 5 = 1 ∨ p % 5 = 4) ∧ IsSL2 5 (↥H ⧸ C)))

@[expose] def A130Fact : Prop :=
  ∀ (p : ℕ), p.Prime → 3 < p → ∀ (P : Type) [Group P],
    Nonempty (P ≃* Multiplicative (Fin 2 → ZMod (p ^ 2))) →
    ∀ f : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* MulAut P, ¬ Function.Injective f

@[expose] def A133TwoFact : Prop :=
  ∀ (p : ℕ), p.Prime → 3 < p → ∀ (L : Type) [Group L] [Finite L] (P : Subgroup L) [P.Normal],
    IsPOnePlusTwo p ↥P → IsSL2 p (L ⧸ P) → 2 < CFSG.Open.pRank p (⊤ : Subgroup L)

@[expose] def L2MultiplierFact : Prop :=
  ∀ r : ℕ, r.Prime → 5 ≤ r → ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
    ∀ (Z : Subgroup X) [Z.Normal], Z ≤ Subgroup.center X → IsPSL 2 r 1 (X ⧸ Z) →
      Nat.card Z ≤ 2

@[expose] def ThreeCoverFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → Nat.card (Subgroup.center X) = 3 →
    A23List (X ⧸ Subgroup.center X) → A36Case2List X

@[expose] def A23SQTKListFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X], SQTKGroup X →
    ∀ (H : Subgroup X) (N : Subgroup ↥H) [N.Normal], IsSimpleGroup (↥H ⧸ N) →
      (∃ a b : ↥H ⧸ N, a * b ≠ b * a) → A23List (↥H ⧸ N)

@[expose] def CatalogStepFact : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → SQTKGroup L →
    Odd (Nat.card (Subgroup.center L)) →
      Nat.card (Subgroup.center L) = 1 ∨ Nat.card (Subgroup.center L) = 3

structure A36CaseBFacts : Prop where
  a129 : A129One
  a130 : A130Fact
  a133 : A133TwoFact
  l2mult : L2MultiplierFact

structure A36Facts : Prop extends A36CaseBFacts where
  threeCover : ThreeCoverFact
  list : A23SQTKListFact
  catalog : CatalogStepFact

structure A36BHyp (X : Type) [Group X] : Prop where
  finite : Finite X
  perfect : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤
  simple : IsSimpleGroup (X ⧸ CFSG.solvableRadical X)
  nonabelian : ∃ a b : X ⧸ CFSG.solvableRadical X, a * b ≠ b * a
  o2 : CFSG.pCore 2 X = ⊥
  rank : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 2
  noncentral : ¬ CFSG.fittingSubgroup X ≤ Subgroup.center X

@[expose] def A36CaseBConclusion (X : Type) [Group X] : Prop :=
  (A36Case3 X ∨ A36Case4 X) ∧ A36Common X ∧ A36Extra X

@[expose] def A36CaseBStatement : Prop :=
  ∀ (X : Type) [Group X], A36BHyp X → A36CaseBConclusion X

end CFSG.Quasithin
