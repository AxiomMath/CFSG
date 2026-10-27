module

public import CFSG.RankThree.GF2n.Smith81.S81CCases
public import CFSG.RankThree.GF2n.Smith81.ESetup
public import CFSG.RankThree.GF2n.Stroth80.Sec3Defs

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

@[expose] def ETacitE3LStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE3L M Q Z B → ∀ B' : Subgroup G, Ctx M Q Z B' →
      NoA2 Q Z (LB M Q B') ∧ GenByB M Q B'

end CFSG.RankThree.GF2n.Smith81
