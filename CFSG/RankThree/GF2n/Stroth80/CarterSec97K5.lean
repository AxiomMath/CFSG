module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.GF2n.Stroth80.Sec5Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

structure Sec97K5 (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (t : G) (T : Subgroup G) : Prop where
  comm_le : ⁅LB M Q B ⊓ hc.CN t, T⁆ ≤ B ⊔ Z
  t_le_sum : T ≤ Vt M (LB M Q B) B Z t ⊔ (Wt Q (Vt M (LB M Q B) B Z t) ⊓ QB B)
  cen_le : ∀ x ∈ T, (∀ l ∈ LB M Q B ⊓ hc.CN t, ⁅l, x⁆ ∈ Z) →
    x ∈ Vt M (LB M Q B) B Z t
  nontriv : ¬ T ≤ Z
  inf_V_le : T ⊓ Vt M (LB M Q B) B Z t ≤ Z

end CFSG.RankThree.GF2n.Stroth80
