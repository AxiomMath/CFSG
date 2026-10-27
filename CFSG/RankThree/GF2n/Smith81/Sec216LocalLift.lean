module

public import CFSG.RankThree.GF2n.Smith81.Bridge
public import CFSG.RankThree.GF2n.Smith81.Sec220Defs

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

structure E3L45World (M Q Z B : Subgroup G) (z v : G) : Prop where
  below : Smith1981Below (Nat.card G)
  rem : RemCfg M Q Z B
  ecase : ∃ t : G, CtxD4 M Q Z B t ∧ (CaseE3L M Q Z B ∨ CaseE4 M Q Z B t ∨ CaseE5 M Q Z B t)
  hz : z ∈ Z
  hz1 : z ≠ 1
  hv : IsDihOddZ Z z v

section World

variable [Finite G] {M Q Z B : Subgroup G} {z v : G}

theorem E3L45World.hStroth (h : E3L45World M Q Z B z v) : StrothHyp M Q Z := h.rem.ctx.hyp

end World

end CFSG.RankThree.GF2n.Smith81
