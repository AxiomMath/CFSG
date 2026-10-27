module

public import CFSG.Dihedral.OriginalNormalizerModel
public import CFSG.Dihedral.OriginalNormalizerCoordinates
public import CFSG.Dihedral.OriginalNormalizerPrimeClass
public import CFSG.Dihedral.OriginalNormalizerFourgroup

public section

namespace CFSG.Milestones

open DihedralBlueprint

theorem gw_original_normalizer_r_pure_projective_shared_fourgroup_and_index_divisor (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (d : OriginalData G)
    (hs : d.Stationarity) (hc : d.CanonicalNormalizers) (hm : d.MaximalOddKernel)
    (hR : d.R ≠ ⊥) (hCN : d.C < d.N) : d.PureProjectiveNormalizer := by
  obtain ⟨e⟩ := d.aSeven_model_of_strict_normalizer hnonab hR hCN
  obtain ⟨f, ht⟩ := d.aSeven_equiv_aligned e
  obtain ⟨i, hi⟩ := d.exists_original_fourgroup_fixed_of_aligned_aSeven_model hR f ht
  have hcycle := d.cycles_of_fixed_original_fourgroup_of_aligned_aSeven_model hR f ht i hi
  refine ⟨hm.2.2.2.1 hR, hm.2.1, ?_, ?_, i, hcycle,
    d.opposite_original_fourgroup_of_stationarity hs hm hR i hcycle, hi,
    d.original_even_rotation_centralizes_R_of_aSeven_model f i hi,
    d.primeSupport_eq_sigma_one_of_aligned_aSeven_model hR f ht,
    d.original_prime_family_control_of_common_cycle hc hR f i hi hcycle⟩
  · rw [show Subgroup.centralizer ({d.t} : Set G) = d.C by
      simpa only [OriginalData.t] using d.centralizer.symm]
    exact inf_eq_right.mpr hm.2.2.1
  · exact d.every_coordinate_of_aligned_aSeven_model hR f ht

end CFSG.Milestones
