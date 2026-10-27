module

public import CFSG.RankThree.GF2n.Stroth80.Sec3Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def Ebar (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal] : Set (Mbar M Q) :=
  {τ | (∃ e : M, (e : Mbar M Q) = τ ∧ IsA2 Q Z (e : G)) ∧
    ∃ x : Mbar M Q, x * τ * x⁻¹ ∈ bar M Q (LB M Q B)}

@[expose] def Xbar (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal] : Subgroup (Mbar M Q) :=
  Subgroup.closure (Ebar M Q Z B)

end CFSG.RankThree.GF2n.Stroth80
