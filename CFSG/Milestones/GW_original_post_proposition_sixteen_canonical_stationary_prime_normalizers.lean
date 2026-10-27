module

public import CFSG.Dihedral.OriginalCanonicalPrimeNormalizers

public section

namespace CFSG.Milestones

open DihedralBlueprint

theorem gw_original_post_proposition_sixteen_canonical_stationary_prime_normalizers (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (d : OriginalData G)
    (hs : d.Stationarity) : d.CanonicalNormalizers := by
  exact d.canonicalNormalizers hnonab hs

end CFSG.Milestones

namespace CFSG.Milestones

open DihedralBlueprint

theorem gw_original_post_proposition_sixteen_canonical_stationary_prime_normalizers_full (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (d : OriginalData G)
    (hs : d.Stationarity) : d.CanonicalNormalizersFull := by
  exact d.canonicalNormalizersFull hnonab hs

end CFSG.Milestones
