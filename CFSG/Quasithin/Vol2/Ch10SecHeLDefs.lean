module

public import CFSG.Open.QuasithinDefs
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open

@[expose] def NoHeLStarF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T K : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaximalLocal T K → quasithinIsFaithfulLocal T K →
    T ≤ Subgroup.normalizer (K : Set G) →
      ¬ Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ≃* CFSG.Blueprint.NativeSporadic.Carrier .He)

end CFSG.Quasithin.Vol2.Ch10
