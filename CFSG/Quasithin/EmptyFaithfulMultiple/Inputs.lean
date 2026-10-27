module

public import CFSG.Quasithin.Vol2.Ch1Xi
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin

@[expose] def Input127Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → CFSG.QuasithinUnique.quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ L : Subgroup G, quasithinIsMaximalLocal T L →
      IsUniqueM (L ⊔ T) (Subgroup.normalizer (conjClosure L T : Set G))

@[expose] def Input137 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → CFSG.QuasithinUnique.quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ X : Subgroup G, IsXiStar T X → IsUniqueM (X ⊔ T) (Subgroup.normalizer (X : Set G))

@[expose] def Input3213 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → CFSG.QuasithinUnique.quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ X : Subgroup G, IsXiStarF T X → IsXiMinus T X

@[expose] def Input1413 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    CFSG.QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → (∀ L : Subgroup G, ¬ quasithinIsFaithfulLocal T L) →
    ∀ H : Subgroup G, InH T H → ∀ U : Subgroup G, IsTwoReducedIn H U →
      perfectCore H ≤ Subgroup.centralizer (U : Set G)

end CFSG.Quasithin.EmptyFaithfulMultiple
