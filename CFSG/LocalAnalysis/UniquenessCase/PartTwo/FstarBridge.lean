module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

theorem fstar_eq_of_generalizedFitting_eq {G : Type} [Group G] {X H : Subgroup G}
    (hXH : X ≤ H) (h : CFSG.generalizedFitting ↥H = X.subgroupOf H) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar H = X := by
  rw [CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar,
    CFSG.Adapters.genFittingFStar_eq_foundations, h,
    Subgroup.map_subgroupOf_eq_of_le hXH]

theorem fstar_eq_self_of_isQuasisimple {G : Type} [Group G] {H : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥H) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar H = H := by
  have hq' : CFSG.IsQuasisimple ↥H := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq
  refine fstar_eq_of_generalizedFitting_eq (X := H) le_rfl ?_
  rw [Subgroup.subgroupOf_self]
  exact CFSG.WholeGroup.generalizedFitting_eq_top_of_isQuasisimple hq'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
