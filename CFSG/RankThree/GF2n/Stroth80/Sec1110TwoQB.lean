module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoEquality

public section

namespace CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G] [Finite G]
variable {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

theorem card_inf_QB_eq_of_two (hc : Ctx M Q Z B) {n x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hx : 1 ≤ x) (hZ : Nat.card Z = 2 ^ x)
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥) :
    Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (2 * n - 2) :=
  (card_bar_LB_eq_sq_iff hc hw (by omega)).mp
    (card_bar_LB_eq_sq hc hw hn hx hZ hLm2 hcenter)

end CFSG.RankThree.GF2n.Stroth80
