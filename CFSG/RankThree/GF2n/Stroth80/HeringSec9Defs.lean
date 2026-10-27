module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.GF2n.Stroth80.Sec9Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

@[expose] def Split95 (M Q Z B : Subgroup G) (t : G) (X Y : Subgroup G) : Prop :=
  IsDirectProdQuot (Rt M (LB M Q B) t) X Y Q ∧ QuotSat Y Q (IsSLModel 2 (Nat.card Z)) ∧
    ∀ x ∈ X, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t

@[expose] def Uline (Z B Y : Subgroup G) : Subgroup G :=
  Z ⊔ ⨆ (y : G) (_ : y ∈ Y), conjSubgroup y B

end HS9

@[expose] def Stroth95Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∃ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y

@[expose] def Sec95N5Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → n = 5 →
      ∃ x ∈ LB M Q B, x ∉ hc.CN t ∧
        ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t

@[expose] def Step95CoreStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → 6 ≤ n → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
      (∀ s ∈ Z0, ∀ g ∈ M, g * s * g⁻¹ ∈ LB M Q B → g * s * g⁻¹ ∈ hc.CN t) →
      (∃ s ∈ Z0, ∃ g ∈ M, g * s * g⁻¹ ∈ LB M Q B ∧ g * s * g⁻¹ ∉ Z0) →
      ∃ x ∈ LB M Q B, x ∉ hc.CN t ∧
        ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t

@[expose] def Sec97HeadStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, HS9.Split95 M Q Z B t X Y →
      hc.CN t ≤ X ∧
      (LB M Q B ⊓ hc.CN t).relIndex (LB M Q B ⊓ X) = Nat.card Z

end CFSG.RankThree.GF2n.Stroth80
