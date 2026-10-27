module

public import CFSG.RankThree.PartTwo.Sec13.Item138N

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU)

@[expose] def K13PZeroElem : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsLThreePi X → CFSG.IsQuasisimple X →
    (∃ j d : X, j ^ 3 = 1 ∧ j ≠ 1 ∧ d ^ 3 = 1 ∧ j * d = d * j ∧ d ∉ Subgroup.zpowers j ∧
      ∃ V : Subgroup X, V ≠ ⊥ ∧ IsPGroup 2 V ∧ j ∈ Subgroup.normalizer (V : Set X)) ∨
    ∃ n : ℕ, Odd n ∧ 1 < n ∧ ¬ 3 ∣ n ∧ Nonempty (X ≃* projSU 3 2 n)

structure PZeroU3 (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L P₀ : Subgroup G)
    (n : ℕ) : Prop where
  sec13 : Sec13Data G A c L
  odd : Odd n
  one_lt : 1 < n
  not_three_dvd : ¬ 3 ∣ n
  iso : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 2 n)
  mem : c ∈ P₀
  le : P₀ ≤ Sec4.thetaQuotCentralizer L
  elem : CFSG.Assembly.IsElemAbelian 3 P₀
  card : Nat.card P₀ = 9

@[expose] def Step13PZeroS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L P₀ : Subgroup G) (n : ℕ),
    PZeroU3 G A c L P₀ n →
      ∃ S₀ : Subgroup G, S₀ ≠ ⊥ ∧ IsPGroup 2 S₀ ∧
        S₀ ≤ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (P₀ : Set G)) ∧
        ¬ S₀ ≤ (aschbacherSolvableCore 3 L).map L.subtype ∧
        ∃ x ∈ P₀, x ∉ Subgroup.zpowers c ∧
          ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (S₀ : Set G)) ⊓
            Subgroup.centralizer ({x} : Set G), Subgroup.zpowers c⁆ ≠ ⊥

@[expose] def Step13PZeroLx : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L P₀ : Subgroup G) (n : ℕ),
    PZeroU3 G A c L P₀ n → ∀ S₀ : Subgroup G, S₀ ≠ ⊥ → IsPGroup 2 S₀ →
    S₀ ≤ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (P₀ : Set G)) →
    ¬ S₀ ≤ (aschbacherSolvableCore 3 L).map L.subtype → ∀ x ∈ P₀, x ∉ Subgroup.zpowers c →
    ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (S₀ : Set G)) ⊓
        Subgroup.centralizer ({x} : Set G), Subgroup.zpowers c⁆ ≠ ⊥ →
      ∃ Lx ∈ thetaComponentsAt 3 x,
        inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({x} : Set G)) ≤ Lx ∧
          c ∈ Subgroup.normalizer (Lx : Set G) ∧ c ∉ Sec4.thetaQuotCentralizer Lx

section Kinds

@[expose] def Step13PZero419 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L P₀ : Subgroup G) (n : ℕ),
    PZeroU3 G A c L P₀ n → ∀ x ∈ P₀, x ∉ Subgroup.zpowers c → ∀ Lx ∈ thetaComponentsAt 3 x,
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({x} : Set G)) ≤ Lx →
      c ∈ Subgroup.normalizer (Lx : Set G) → c ∉ Sec4.thetaQuotCentralizer Lx →
        KFacts.InducesStdKind Lx c .field ∨ KFacts.InducesStdKind Lx c .graphField

end Kinds

@[expose] def Step138NoCubeRootC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Hyp138 A c L E → Sec8.IsZ3PGLThreePi (lBarA c L E) → ∀ F : Subgroup G, IsF138N L E F →
    (∀ F' : Subgroup G, CFSG.Assembly.IsElemAbelian 3 F' → F ≤ F' → F' = F) →
    ∀ P : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.normalizer (Subgroup.zpowers c : Set G)) →
      E ⊔ F ≤ P → P ≤ Subgroup.normalizer (L : Set G) →
      (∀ v ∈ P ⊓ Sec4.thetaQuotCentralizer L, v ^ 3 = 1 → v ∈ Subgroup.zpowers c) →
      ∀ w ∈ P ⊓ Sec4.thetaQuotCentralizer L, (∀ f ∈ F, f * w = w * f) → w ^ 3 ≠ c

end CFSG.RankThree.PartTwo.Sec13
