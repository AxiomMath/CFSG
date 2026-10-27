module

public import CFSG.Dihedral.OriginalPrimeStationarity
public import CFSG.Dihedral.OriginalOneCycleFixedKernel
public import CFSG.Dihedral.IndexTwoPGLCoordinates

public section

namespace CFSG.Milestones

open DihedralBlueprint

theorem gw_original_post_proposition_sixteen_all_prime_stationarity_and_no_growth (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (d : OriginalData G)
     : d.Stationarity := by
  have hprime := d.prime_stationarity_and_no_growth hnonab
  refine ⟨hprime.1, hprime.2.1, hprime.2.2.1, hprime.2.2.2.1,
    hprime.2.2.2.2, d.cycling_local_core_and_inverted hnonab, ?_, ?_⟩
  · intro H hH hSH
    refine ⟨?_, d.both_cycles_quotient_and_indexTwo hnonab H hH hSH⟩
    intro i j hij hi hj
    exact ⟨d.one_cycle_fixed_intersection hnonab H hSH i j hij hi hj,
      d.one_cycle_PGL_and_indexTwo H hH hSH i j hi hj⟩
  · intro H hH hCH _hc
    exact d.centralizer_overgroup_not_both_cycles H hH hCH

end CFSG.Milestones
