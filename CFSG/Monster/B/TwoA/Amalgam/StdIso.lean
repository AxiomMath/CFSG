module

public import CFSG.Monster.B.TwoA.Amalgam.StdIsoNative
public import CFSG.Monster.B.TwoA.Amalgam.StdIsoStandard

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.E6.StdF4

theorem native_standard_F4_initial_opposite_foundation_isometry
    {δ : Chamber → Chamber → WeylGroup .F4} (hδ : IsWeylDistanceBuilding (coxeterSystem .F4) δ)
    (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber),
      chamberCS.adj i x y ↔ δ x y = 1 ∨ δ x y = (coxeterSystem .F4).simple i)
    {c d : Chamber} {c' d' : C2E6Std.stdChamber}
    (hcd : δ c d = longest (coxeterSystem .F4) Set.univ)
    (hcd' : stdDistanceF4 c' d' = longest (coxeterSystem .F4) Set.univ) :
    ∃ φ : Chamber → C2E6Std.stdChamber,
      IsWeylIsometry δ stdDistanceF4 (foundation (coxeterSystem .F4) δ 2 c ∪ {d})
        (foundation (coxeterSystem .F4) stdDistanceF4 2 c' ∪ {d'}) φ ∧ φ c = c' ∧ φ d = d' :=
  exists_initial_isometry_of_hasClassicalEnds hδ isWeylDistanceBuilding_stdDistanceF4
    (hasClassicalEnds_native hδ hadj) hasClassicalEnds_std encard_panel_one_std hcd hcd'

end CFSG.Monster.B.TwoA.Amalgam
