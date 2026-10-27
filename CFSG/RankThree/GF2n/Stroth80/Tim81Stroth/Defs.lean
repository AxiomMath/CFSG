module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G]

abbrev Hbar (M Q Z : Subgroup G) [(Q.subgroupOf M).Normal] : Type :=
  ↥(bar M Q (H0 M Z))

abbrev VbarPrime (M Q Z0 : Subgroup G) [(Q.subgroupOf M).Normal] :
    Subgroup (↥M ⧸ Q.subgroupOf M) :=
  bar M Q Z0

theorem NormH0_le_H0 (M Z Z0 : Subgroup G) : NormH0 M Z Z0 ≤ H0 M Z :=
  inf_le_left

theorem MbarPrimeLe (M Q Z Z0 : Subgroup G) [(Q.subgroupOf M).Normal] :
    bar M Q (NormH0 M Z Z0) ≤ bar M Q (H0 M Z) :=
  Subgroup.map_mono fun _ hx => NormH0_le_H0 M Z Z0 hx

abbrev MbarPrime (M Q Z Z0 : Subgroup G) [(Q.subgroupOf M).Normal] :
    Subgroup (Hbar M Q Z) :=
  (bar M Q (NormH0 M Z Z0)).subgroupOf (bar M Q (H0 M Z))

end CFSG.RankThree.GF2n.Stroth80
