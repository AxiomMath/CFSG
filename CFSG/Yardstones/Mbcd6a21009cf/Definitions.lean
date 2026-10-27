module

public import CFSG.Quasithin.H13.Statements

public section

namespace CFSG.Yardstones.Mbcd6a21009cf

@[expose] def QTH13MaximalLocalCatalogAssembly : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G),
    CFSG.Quasithin.H13.QTH13 G T L → CFSG.Open.quasithinIsMaximalLocal T L →
      CFSG.Blueprint.Catalog G

end CFSG.Yardstones.Mbcd6a21009cf
