module

public import CFSG.RankThree.GF2n.Tim79a34TwoEnd

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

@[expose] def NTQEInStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), TwoEndHyp M V Q P H →
    Subgroup.center (Xbar V H) = ⊥ →
    (∃ n : ℕ, 3 ≤ n ∧ Nonempty (↥(StatedSp n (GaloisField 2 1)) ≃* XbarZ V H)) →
    P.relIndex Q = 2 →
    (∀ (N : Subgroup G) [N.Normal], IsPGroup 2 (G ⧸ N) → Q ≤ N) → False

end CFSG.RankThree.GF2n.Tim79a
