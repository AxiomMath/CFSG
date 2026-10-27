module

public import CFSG.Yardstones.Mbcd6a21009cf.Definitions
public import CFSG.Quasithin.H13.AssemblyTheoremD
public import CFSG.Quasithin.H13.LocDblSporadic
public import CFSG.Adapters.CatalogAgree
public import CFSG.Quasithin.H13.AssemblyVocab

public section

namespace CFSG.Yardstones.Mbcd6a21009cf

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13

theorem catalog_of_qtH13_of_localDoubleEmbeddingExclusion (hD : LocalDoubleEmbeddingExclusion)
    (hH13 : QTH13MaximalLocalCatalogAssembly) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hQ : quasithinIsQTKECat G) (T : Sylow 2 G)
    (hLf : ∃ L : Subgroup G, CFSG.Open.quasithinIsFaithfulLocal (T : Subgroup G) L) :
    CFSG.Blueprint.Catalog G := by
  have hT : quasithinIsSylowTwo (T : Subgroup G) := ⟨T.isPGroup', T.not_dvd_index⟩
  rcases excluded_or_preferred_local hD inferInstance hnonab hQ hT
      (faithful_maximal_local_nonempty hD inferInstance hnonab hQ hT hLf) with h | ⟨L, hL, hH⟩
  · exact h
  · exact hH13 G T L hH hL.1

theorem qt_faithful_local_nonempty_classification_of_qtH13
    (hH13 : QTH13MaximalLocalCatalogAssembly)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hqtke : CFSG.Assembly.Quasithin.quasithinIsQTKE G) (T : Sylow 2 G)
    (hLf : ∃ L : Subgroup G,
      CFSG.Assembly.Quasithin.quasithinIsFaithfulLocal (T : Subgroup G) L) :
    CFSG.Assembly.InCatalog G :=
  have hB := QTFaithfulEmptyTauCeti.catalogAgree
  (hB G hnonab).2 (catalog_of_qtH13_of_localDoubleEmbeddingExclusion
    LocDbl.local_double_embedding_exclusion hH13 hnonab
    ⟨QTFaithfulEmptyTauCeti.kProper_catalog_of_agree hB hqtke.1, hqtke.2.1, hqtke.2.2⟩ T
    (hLf.imp fun _ h => quasithinIsFaithfulLocal_open_iff.mpr h))

end CFSG.Yardstones.Mbcd6a21009cf
