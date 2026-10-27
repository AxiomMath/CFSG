module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.RankThree.GF2n.Stroth80.Sec8Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Statements

@[expose] def Stroth53FixBStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
    (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
    ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      ∀ x ∈ Sec8W1 M Q Z B t r,
        (∀ l ∈ LB M Q B, ⁅l, x⁆ ∈ Sec8V1 M Q Z B t r) →
          x ∈ (QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r

@[expose] def Stroth53FixCStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
    (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
    ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      ∀ x ∈ Sec8W1 M Q Z B t r,
        (∀ l ∈ LB M Q (conjSubgroup r B), ⁅l, x⁆ ∈ Sec8V1 M Q Z B t r) →
          x ∈ (QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r

@[expose] def Stroth53IndecVoneStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
    (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
    ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      IsIndecSec (Rt M (LB M Q B) t) (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)) Z

end Statements

end CFSG.RankThree.GF2n.Stroth80
