module

public import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S10.PerfectSubgroupsNormalizeQuotientComponents

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank

theorem p_coprime_local_theta_component_quotient_normalization_frontier :
    PCoprimeLocalThetaComponentQuotientNormalizationFrontier := by
  intro H _ _ _ hH p _ _ x _ Y hY _ L hL
  obtain ⟨L₀, hL₀, rfl⟩ := hY
  have := hL₀.1
  have hYperf : Group.IsPerfect ↥(L₀.map (Subgroup.centralizer ({x} : Set H)).subtype) :=
    Group.IsPerfect.map _
  exact perfect_subgroups_normalize_quotient_components_at_rank_three H hH
    (aschbacherSolvableCore p H) _ (Group.IsPerfect.map (QuotientGroup.mk' _)) L hL

end CFSG.RankThree.PartOne
