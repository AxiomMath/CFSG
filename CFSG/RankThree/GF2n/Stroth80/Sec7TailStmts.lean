module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmt
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Sec713YStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∃ y ∈ Rt M (LB M Q B) t, y ∉ Q ∧ y ^ 3 ∈ Q ∧ ∀ x ∈ hc.CN t, ⁅y, x⁆ ∈ Q → x ∈ Z0

@[expose] def Sec7WVMinOrderStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t →
    ∀ A : Subgroup G, Vt M (LB M Q B) B Z t ≤ A → A ≤ Wt Q (Vt M (LB M Q B) B Z t) →
      (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A = A) → A ≠ Vt M (LB M Q B) B Z t →
      ∀ m : ℕ, 2 ≤ m →
    (OmegaMinusNat hc t m →
      Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card Z ^ (2 ^ m) ≤ Nat.card A) ∧
    (OmegaPlusNat hc t m → 3 ≤ m →
      Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card Z ^ (2 ^ (m - 1)) ≤ Nat.card A)

@[expose] def Sec715CentStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t →
    (OmegaPlusNat hc t 3 ∨ OmegaPlusNat hc t 4) →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q → IsCentrePre Z0 (hc.CN t) Q →
    ∀ k : Mbar M Q, IsPGroup 2 (Subgroup.zpowers k) →
      (∀ x ∈ bar M Q (hc.CN t), k * x = x * k) → k ∈ bar M Q Z0

@[expose] def Sec715ConjStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 4 → n = 16 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q → IsCentrePre Z0 (hc.CN t) Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    ∃ g ∈ M, conjSubgroup g Z0 ≤ hc.CN t ∧ conjSubgroup g Z0 ≠ Z0

@[expose] def Sec715IrrStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 4 → n = 16 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q → IsCentrePre Z0 (hc.CN t) Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    ∀ A : Subgroup G, Z0 ≤ A → A ≤ hc.CN t →
      (∀ k ∈ NormH0 M Z Z0, conjSubgroup k A = A) → A = Z0 ∨ A = hc.CN t

@[expose] def Sec717MoveStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 3 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q → IsCentrePre Z0 (hc.CN t) Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    ∀ L : Subgroup G, Sec717L hc t Z0 L → (∀ k ∈ NormH0 M Z Z0, conjSubgroup k L = L) →
    (∃ h ∈ H0 M Z, conjSubgroup h Z0 ≤ NormH0 M Z Z0 ∧ ¬ conjSubgroup h Z0 ≤ hc.CN t) →
    ¬ NormH0L M Z L ≤ NormH0 M Z Z0

@[expose] def Ext1VanishingD4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → OmegaPlusNat hc t 4 → n = 16 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q → IsCentrePre Z0 (hc.CN t) Q →
    (∀ A : Subgroup G, Z0 ≤ A → A ≤ hc.CN t →
        (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A = A) →
        ∃ A' : Subgroup G, Z0 ≤ A' ∧ A' ≤ hc.CN t ∧
          (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A' = A') ∧ A ⊔ A' = hc.CN t ∧ A ⊓ A' = Z0) ∧
    (∀ A : Subgroup G, Vt M (LB M Q B) B Z t ≤ A → A ≤ Wt Q (Vt M (LB M Q B) B Z t) →
        (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A = A) →
        ∃ A' : Subgroup G, Vt M (LB M Q B) B Z t ≤ A' ∧ A' ≤ Wt Q (Vt M (LB M Q B) B Z t) ∧
          (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A' = A') ∧
          A ⊔ A' = Wt Q (Vt M (LB M Q B) B Z t) ∧ A ⊓ A' = Vt M (LB M Q B) B Z t)

@[expose] def Sec715SplitStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → OmegaPlusNat hc t 4 → n = 16 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ¬ ⁅hc.CN t, hc.CN t⁆ ≤ Q → ∀ Zn : Subgroup G, IsCentrePre Zn (hc.CN t) Q → Zn ≠ Z0 →
    ∃ Y : Subgroup G, Q ≤ Y ∧ Y ≤ Zn ∧ (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r Y = Y) ∧
      Y ⊓ Z0 = Q ∧ Y ⊔ Z0 = Zn

end CFSG.RankThree.GF2n.Stroth80
