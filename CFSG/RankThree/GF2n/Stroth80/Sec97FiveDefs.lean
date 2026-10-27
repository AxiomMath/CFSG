module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

@[expose] def planeST (M Q Z B X : Subgroup G) (nn g : G) : Subgroup G :=
  ⁅Vt M (LB M Q B) B Z nn, conjSubgroup g (LB M Q B ⊓ X)⁆ ⊔ Z

@[expose] def pointT (hc : Ctx M Q Z B) (X Y : Subgroup G) (nn g : G) : Subgroup G :=
  planeST M Q Z B X nn g ⊓ CQtGrp hc (LB M Q B ⊓ Y)

structure Sec97K13 (hc : Ctx M Q Z B) (t : G) (X Y : Subgroup G) (r nn g : G) : Prop where
  g_mem : g ∈ M
  inf_eq : Vt M (LB M Q B) B Z t ⊓ Vt M (LB M Q B) B Z nn = Uline Z (conjSubgroup r B) Y
  sup_eq : Uline Z (conjSubgroup r B) Y ⊔ planeST M Q Z B X nn g = Vt M (LB M Q B) B Z nn
  inf_Z : Uline Z (conjSubgroup r B) Y ⊓ planeST M Q Z B X nn g = Z
  Y_le : Y ≤ Subgroup.normalizer (planeST M Q Z B X nn g : Set G)
  point : ∃ m ∈ M, pointT hc X Y nn g = conjSubgroup m B ⊔ Z

end HS9

end CFSG.RankThree.GF2n.Stroth80
