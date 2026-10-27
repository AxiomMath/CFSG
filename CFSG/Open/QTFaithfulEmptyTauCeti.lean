module

public import CFSG.Milestones.QT_faithful_local_empty_classification

public section

namespace CFSG.Open.QTFaithfulEmptyTauCeti

open CFSG.Assembly CFSG.Assembly.Quasithin

@[expose] def CatalogAgree : Prop :=
  CatalogAgreeOn InCatalog Blueprint.Catalog

theorem kProper_catalog_of_agree (hB : CatalogAgree) {G : Type} [Group G] [Finite G]
    (hK : KProper InCatalog G) : KProper Blueprint.Catalog G :=
  hK.of_catalogAgree hB

theorem quasithinIsQTKECat_of_agree (hB : CatalogAgree) {G : Type} [Group G] [Finite G]
    (h : CFSG.Assembly.Quasithin.quasithinIsQTKE G) : QuasithinUnique.quasithinIsQTKECat G :=
  QTKEOver.of_catalogAgree hB h

theorem qt_faithful_local_empty_classification_of_agree
    (hB : CatalogAgree)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hqtke : CFSG.Assembly.Quasithin.quasithinIsQTKE G) (T : Sylow 2 G)
    (hMT : ∃ M₁ M₂ : Subgroup G, M₁ ≠ M₂ ∧
      CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M₁ ∧
      CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M₂ ∧
      (T : Subgroup G) ≤ M₁ ∧ (T : Subgroup G) ≤ M₂)
    (hLf : ∀ L : Subgroup G,
      ¬ CFSG.Assembly.Quasithin.quasithinIsFaithfulLocal (T : Subgroup G) L) :
    InCatalog G :=
  (hB G hnonab).2 (Milestones.qt_faithful_local_empty_classification G hnonab
    (quasithinIsQTKECat_of_agree hB hqtke) T hMT hLf)

end CFSG.Open.QTFaithfulEmptyTauCeti
