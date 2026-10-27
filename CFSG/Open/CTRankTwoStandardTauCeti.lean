module

public import CFSG.Milestones.CT_rank_two_standard_recognition_frontier
public import CFSG.Open.CTInitialFrontierTauCeti

public section

namespace CFSG.Open.CTRankTwoStandardTauCeti

open CFSG.Assembly

theorem ct_rank_two_standard_recognition_frontier_models_tauCeti_of_bridge
    (hbridge : CatalogImp InCatalog CFSG.Blueprint.Catalog)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : IsKProper G)
    (L : Subgroup G) (hL : standardComponentIsStandard L)
    (hrank : 2 ≤ pRank 2 (Subgroup.centralizer (L : Set G))) :
    (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
      (Blueprint.NativeSporadic.IsSporadic G .J2 ∨ Blueprint.NativeSporadic.IsSporadic G .Suz ∨
        Blueprint.NativeSporadic.IsSporadic G .He ∨ Blueprint.NativeSporadic.IsSporadic G .Ru ∨
        Blueprint.NativeSporadic.IsSporadic G .Co1) :=
  Milestones.ct_rank_two_standard_recognition_frontier_models G hnonab
    (CFSG.Open.CTInitialFrontierTauCeti.kProper_catalog_of_bridge hbridge hK) L hL hrank

end CFSG.Open.CTRankTwoStandardTauCeti
