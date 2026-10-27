module

public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.LocalAnalysis.SteinbergBQ

open CFSG

theorem generalized_fitting_subnormal_monotone {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (hH : H.IsSubnormal) :
    (generalizedFitting H).map H.subtype ≤ generalizedFitting G := by
  simp only [CFSG.generalizedFitting.eq_sup, CFSG.layer.eq_sSup]
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rw [ComponentClassification.SmallLocal.fitting_subnormal_intersection hH]
    exact inf_le_right.trans le_sup_left
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hcomp : K.map H.subtype ∈ {L : Subgroup G | IsComponent L} :=
      ComponentInitial.component_subnormal_lift hH hK
    exact (le_sSup hcomp).trans le_sup_right

end CFSG.LocalAnalysis.SteinbergBQ
