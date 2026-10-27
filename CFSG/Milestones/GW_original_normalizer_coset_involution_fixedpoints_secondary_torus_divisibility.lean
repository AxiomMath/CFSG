module

public import CFSG.Dihedral.OriginalCosetBounds
public import CFSG.Dihedral.OriginalPureModel

public section

namespace CFSG.Milestones

open DihedralBlueprint

theorem gw_original_normalizer_coset_involution_fixedpoints_secondary_torus_divisibility (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (d : OriginalData G)
    (hs : d.Stationarity) (hc : d.CanonicalNormalizers) (hm : d.MaximalOddKernel)
    (hp : d.PureProjectiveNormalizer) (hR : d.R ≠ ⊥) (hCN : d.C < d.N) : d.CosetBounds := by
  obtain ⟨e⟩ := d.aSeven_model_of_pure hnonab hp hR
  obtain ⟨f, ht⟩ := d.aSeven_equiv_aligned e
  exact d.cosetBounds_of_aligned_aSeven_model hp hR f ht

end CFSG.Milestones
