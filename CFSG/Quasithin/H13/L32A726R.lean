module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique

@[expose] def KG14726Sz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G), Lemma115Cases L z →
    CFSG.IsQuasisimple ↥L → ¬ 3 ∣ Nat.card L →
    ∀ P : Subgroup (MulAut ↥L), IsPGroup 3 P → IsCyclic P

end CFSG.Quasithin.H13
