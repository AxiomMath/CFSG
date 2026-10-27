module

public import CFSG.Dihedral.OriginalOvergroupQuotients

public section

namespace CFSG.Milestones

open DihedralBlueprint

theorem gw_original_maximal_odd_s_invariant_r_and_normalizer_core (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (d : OriginalData G)
    (hs : d.Stationarity) (hc : d.CanonicalNormalizers) : d.MaximalOddKernel := by
  refine ⟨?_, d.normalizer_oddCore hc, d.centralizer_le_normalizer,
    d.normalizer_ne_top, ?_, d.strict_overgroup_quotients hc,
    d.normalizer_eq_centralizer_or_coordinates hc⟩
  · intro W hodd hW
    exact ⟨d.primeSupport_of_normalized_odd W hodd hW,
      d.odd_overgroup_eq hc W hodd hW⟩
  · intro H _ hCH
    exact ⟨d.overgroup_le_normalizer_iff hc H hCH,
      fun hHN => ⟨d.oddCoreOf_eq_R_of_le_normalizer hc H hCH hHN,
        d.two_quotient_iff_eq_centralizer hc H hCH⟩⟩

end CFSG.Milestones
