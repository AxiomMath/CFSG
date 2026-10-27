module

public import CFSG.RankThree.GF2n.Smith81.ESetup
public import CFSG.RankThree.GF2n.Smith81.S81CCases
public import CFSG.RankThree.GF2n.Smith81.S81D6W

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80

@[expose] def E4G1Statement :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE4 M Q Z B →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = Nat.card Z ∧
        ∃ θ : Lgen M (LB M Q B) →* D6Spin.EAut0 K,
          Function.Surjective θ ∧ ∀ s, θ s = 1 ↔ (s : G) ∈ Q

end CFSG.RankThree.GF2n.Smith81
