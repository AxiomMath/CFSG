module

public import CFSG.Yardstones.Mc8b1839a864e.Definitions
public import CFSG.LocalAnalysis.QuasithinUnique.QTKEAssemblyUnique
public import CFSG.Adapters.CatalogAgree

public section

namespace CFSG.Yardstones.Mc8b1839a864e

open CFSG.Quasithin CFSG.QuasithinUnique

theorem faithfulLocalNonemptyCat_of_tauCeti
    (hD : FaithfulLocalNonemptyTauCetiStatement) : FaithfulLocalNonemptyCat := by
  intro G _ _ _ hnonab hqtke T hLf
  have hB := CFSG.Open.QTFaithfulEmptyTauCeti.catalogAgree
  refine (hB G hnonab).1 (hD G hnonab ⟨fun K L hKt hL _ hs hn => ?_, hqtke.2.1, hqtke.2.2⟩ T hLf)
  have := hs
  exact (hB _ hn).2 (hqtke.1 K L hKt hL hs hn)

theorem cls_qtke_classification_of_milestones
    (hD : FaithfulLocalNonemptyTauCetiStatement) (hE : FaithfulLocalEmptyCat)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hqtke : QuasithinUnique.quasithinIsQTKECat G) : Blueprint.Catalog G :=
  cls_qtke_classification_of_D_E hE (faithfulLocalNonemptyCat_of_tauCeti hD) G hnonab hqtke

end CFSG.Yardstones.Mc8b1839a864e
