module

public import CFSG.RankThree.PartOne.KP.CatalogRank
public import CFSG.RankThree.PartOne.KP.J4
public import CFSG.RankThree.PartOne.KP.SporadicRank
public import CFSG.RankThree.PartOne.KP.MReduction
public import CFSG.RankThree.PartOne.KP.J4Coprime

public section

namespace CFSG.RankThree.PartOne

open CFSG.Blueprint.NativeSporadic (Carrier)

theorem j4CoprimeAutomorphismSubgroupsTrivial : J4CoprimeAutomorphismSubgroupsTrivial :=
  fun T _ _ _ hnab hJ4 A hA => j4_coprime_automorphism_subgroups_trivial T hnab hJ4 A hA

theorem original_coprime_catalog_component_local_core_centralization_of_data
    (hdata : SporadicCoprimeRankData)
    (hB : SectionsForceEvenRankFour (Carrier .B))
    (hM : SimplePresentationMSectionsForceEvenRankFour)
    (hJ4 : J4CoprimeAutomorphismSubgroupsTrivial) :
    OriginalCoprimeCatalogComponentLocalCoreCentralization :=
  original_coprime_catalog_component_local_core_centralization_of_inputs
      (catalogCoprimeAutomorphismRankOneOrJ4BM_of_sporadic
          (fun s hs4 hsB hsM => sporadicCoprimeRank_of_data hdata s ⟨hs4, hsB, hsM⟩)) hB hM
      (j4_coprime_normalized_component_centralization_of_automorphisms hJ4)

theorem original_coprime_catalog_component_local_core_centralization_of_B_section
    (hdata : SporadicCoprimeRankData)
    (hB : SectionsForceEvenRankFour (Carrier .B))
    (hMB : SimplePresentationMHasBSection) :
    OriginalCoprimeCatalogComponentLocalCoreCentralization :=
  original_coprime_catalog_component_local_core_centralization_of_data hdata hB
    (simplePresentationM_sections_of_B_section hB hMB) j4CoprimeAutomorphismSubgroupsTrivial

end CFSG.RankThree.PartOne
