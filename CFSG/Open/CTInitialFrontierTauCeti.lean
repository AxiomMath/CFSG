module

public import CFSG.Milestones.CT_initial_standard_component_frontier
public import CFSG.RankThree.PartOne.TCB.Final

public section

namespace CFSG.Open.CTInitialFrontierTauCeti

open CFSG.Assembly

theorem kProper_catalog_of_bridge
    (hbridge : CatalogImp InCatalog CFSG.Blueprint.Catalog)
    {G : Type} [Group G] [Finite G] (hK : KProper InCatalog G) :
    KProper CFSG.Blueprint.Catalog G :=
  hK.of_catalogImp hbridge

theorem initial_standard_component_frontier_of_bridge
    (hbridge : CatalogImp InCatalog CFSG.Blueprint.Catalog)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hrank : 3 ≤ twoRank G)
    (hcomp : IsComponentType G) (hB : ComponentType.LocalBProperty G) :
    (∃ t : G, orderOf t = 2 ∧ ∃ L : Subgroup G,
        IsComponentOf L (Subgroup.centralizer ({t} : Set G)) ∧
          ComponentType.IsStandardSubgroup L) ∨
      (∃ z : G, orderOf z = 2 ∧ ∃ J : Subgroup G,
        IsComponentOf J (Subgroup.centralizer ({z} : Set G)) ∧ z ∈ J ∧
          ∃ r : ℕ, 3 ≤ r ∧ ∃ S : Sylow 2 J,
            Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) := by
  have hfrontier := Milestones.ct_initial_standard_component_frontier G hnonab
    (kProper_catalog_of_bridge hbridge hK) hrank hcomp hB
  simpa only [CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open]
    using hfrontier

theorem initial_standard_component_frontier
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hrank : 3 ≤ twoRank G)
    (hcomp : IsComponentType G) (hB : ComponentType.LocalBProperty G) :
    (∃ t : G, orderOf t = 2 ∧ ∃ L : Subgroup G,
        CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({t} : Set G)) ∧
          ComponentType.IsStandardSubgroup L) ∨
      (∃ z : G, orderOf z = 2 ∧ ∃ J : Subgroup G,
        CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({z} : Set G)) ∧ z ∈ J ∧
          ∃ r : ℕ, 3 ≤ r ∧ ∃ S : Sylow 2 J,
            Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) := by
  simpa only [CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open] using
    initial_standard_component_frontier_of_bridge RankThree.PartOne.TCB.tauCetiCatalogBridge G
      hnonab hK hrank hcomp hB

end CFSG.Open.CTInitialFrontierTauCeti
