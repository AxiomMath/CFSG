module

public import CFSG.Open.QTFaithfulEmptyTauCeti

public section

namespace CFSG.Open.QTH13MaximalLocalTauCeti

open CFSG.Assembly CFSG.Open.QTFaithfulEmptyTauCeti CFSG.Quasithin
open scoped MatrixGroups

theorem kProper_inCatalog_of_agree (hB : CatalogAgree) {G : Type} [Group G] [Finite G]
    (hK : KProper Blueprint.Catalog G) : KProper InCatalog G :=
  hK.of_catalogImp (CatalogAgreeOn.rev hB)

end CFSG.Open.QTH13MaximalLocalTauCeti
