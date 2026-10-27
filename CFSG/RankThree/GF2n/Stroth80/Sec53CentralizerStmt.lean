module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement


@[expose] def Sec53CentralizerW1Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → SpNat hc t →
    ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
    ∀ (C N V W₁ V₁ : Subgroup G), C = conjSubgroup r B → N = hc.CN t →
      V = Vt M (LB M Q B) B Z t → V₁ = Vone Q B C V → W₁ = Wt Q V₁ →
      ∀ y ∈ W₁, (∀ s ∈ N, ⁅s, y⁆ ∈ Z) → y ∈ V₁

end CFSG.RankThree.GF2n.Stroth80
