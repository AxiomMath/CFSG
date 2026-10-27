module

public import CFSG.Monster.Tri.LeechModelRho
public import CFSG.Monster.Tri.LeechModelEight

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Tri.Leech

open SimpleGraph CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Generated CFSG.Monster.GMS
  CFSG.Monster.B CFSG.Monster.B.Short CFSG.YGroups

theorem tStarG_mul_self : tStarG * tStarG = 1 := Subtype.ext tStar_mul_self

theorem tStarG_ne_one : tStarG ≠ 1 := fun h => tStar_ne_one (congrArg Subtype.val h)

theorem ne_one_of_isConj_tStarG {a : Gmat} (ha : IsConj tStarG a) : a ≠ 1 :=
  ne_one_of_isConj tStarG_ne_one ha

variable {a : Gmat}

theorem quad_null_twoAGraph_of_twoBInEight
    (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (ha : IsConj tStarG a) (hE8 : TwoBInEight a xmatG) {x y u : ConjVert a}
    (hxy : (twoAGraph a).Adj x y) (hxu : (twoAGraph a).Adj x u) (hyu : (twoAGraph a).Adj y u)
    (hL : permClosure (longTri a) x y u) :
    MarkedHomotopic (longTri a) ((shortStruct_twoAGraph ha2 ha1).quad hxy hxu hyu hL) .nil :=
  quad_null_twoAGraph_of_two_B ha2 ha1 ha
    (fun hxy hxu hyu hL => isConj_xmatG_of_longTri ha2 ha1 ha hE8 hxy hxu hyu hL)
    (exists_rho_of_commute ha) (fun {_} hr _ hx => exists_lift_of_commonNeighbors ha2 ha hr hx)
    hxy hxu hyu hL

end CFSG.Monster.Tri.Leech
