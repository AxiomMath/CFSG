module

public import CFSG.OddTranspositions.AscTheoremTwo
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.OddTranspositions.SixEight
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

@[expose] def Theorem8_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), HypothesisC D →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → ¬ O4PairData G D →
    ∀ u w v : G, IsTriangle D u w v → IsThirdKind u w v →
      ∃ d ∈ D, Commute d u ∧ Commute d v ∧ Commute d w

@[expose] def Lemma8_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), IsNormalSet D → IsOddTransp D →
    ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4 →
      Group.IsSolvable (Subgroup.closure ({u, w, v} : Set G))

@[expose] def Theorem8_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → ¬ O4PairData G D →
    ∀ β ∈ blockClass hC.alpha, ∀ γ ∈ blockClass hC.alpha,
      β = γ ∨ γ ∈ Dalpha D β ∨ ∃ δ ∈ Dalpha D β, δ ∈ Dalpha D γ

@[expose] def Lemma8_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    (¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n)) →
    ∀ β ∈ Dalpha D hC.alpha, ∀ b ∈ β, ∀ x ∈ CFSG.pCore 2 (Halpha D hC.alpha),
      (x : G) * b * (x : G)⁻¹ ∈ β → (x : G) * b * (x : G)⁻¹ = b

@[expose] def Theorem9_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    CFSG.solvableRadical (Halpha D hC.alpha) = Subgroup.center (Halpha D hC.alpha) →
    CFSG.BenderSuzuki.IsBenderGroup
      (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) →
    ∃ f : ℕ, 2 ≤ f ∧
      Nonempty (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃*
        CFSG.Theory.Comparator.PSL2Model f) ∧
      (Nonempty (G ≃* L2Wreath f 2) ∨
        (Nonempty (↥(commutator G) ≃* CFSG.Theory.Comparator.PSL2Model (2 * f)) ∧
          (commutator G).index = 2))

@[expose] def Theorem10_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    CFSG.solvableRadical (Halpha D hC.alpha) = Subgroup.center (Halpha D hC.alpha) →
    ∀ f n : ℕ, 2 ≤ f → 5 ≤ n →
      Nonempty (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n) →
      Nonempty (G ≃* L2Wreath f (n + 2))

@[expose] def Theorem11_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    ¬ (∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) →
    (CFSG.solvableRadical (Halpha D hC.alpha)).map
        (QuotientGroup.mk' (CFSG.pCore 2 (Halpha D hC.alpha))) =
      Subgroup.center (Halpha D hC.alpha ⧸ CFSG.pCore 2 (Halpha D hC.alpha))

end CFSG.OddTranspositions.PartThree
