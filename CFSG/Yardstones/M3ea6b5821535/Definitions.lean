module

public import CFSG.Blueprint.NativeCatalog

public section

namespace CFSG.Yardstones.M3ea6b5821535

@[expose] def CatNativeConverse : Prop :=
  ∀ (G : Type) [Group G], Blueprint.NativeCatalog G →
    Finite G ∧ Nontrivial G ∧ IsSimpleGroup G

@[expose] def CatSimpleCatalogNativeTransport : Prop :=
  ∀ (G : Type) [Group G] [IsSimpleGroup G], Blueprint.Catalog G → Blueprint.NativeCatalog G

end CFSG.Yardstones.M3ea6b5821535
