module

public import CFSG.Monster.Tri.LeechModelMaster
public import CFSG.Monster.Tri.LeechModelEightGMS

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Tri.Leech

open SimpleGraph CFSG.Monster.Generated CFSG.Monster.GMS CFSG.YGroups

variable {d₀ : CFSG.Blueprint.NativeSporadic.B}

theorem twoBInEight_Gmat
    (I : GMSInterfaces d₀ Gmat) (hG : GMSF1Type d₀ tStarG xmatG) {a : Gmat}
    (ha : IsConj tStarG a) : TwoBInEight a xmatG :=
  (TwoBInEight.congr ha (IsConj.refl xmatG)).1 (twoBInEight_of_gmsF1Type I hG)

variable {a : Gmat}

theorem quad_null_twoAGraph_of_interfaces
    (I : GMSInterfaces d₀ Gmat)
    (hG : GMSF1Type d₀ tStarG xmatG) (ha2 : a * a = 1) (ha1 : a ≠ 1) (ha : IsConj tStarG a)
    {x y u : ConjVert a} (hxy : (twoAGraph a).Adj x y) (hxu : (twoAGraph a).Adj x u)
    (hyu : (twoAGraph a).Adj y u) (hL : permClosure (longTri a) x y u) :
    MarkedHomotopic (longTri a) ((shortStruct_twoAGraph ha2 ha1).quad hxy hxu hyu hL) .nil :=
  quad_null_twoAGraph_of_twoBInEight ha2 ha1 ha (twoBInEight_Gmat I hG ha) hxy hxu hyu hL

end CFSG.Monster.Tri.Leech
