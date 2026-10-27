module

public import CFSG.Quasithin.EmptyFaithful.Gap6R2Base

public section

namespace CFSG.Quasithin.Gap6R2

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def NonBorelL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → Lemma1515Concl T Mc M → Lemma1517Concl T Mc M →
    Lemma1518Concl T Mc M → Lemma1519Concl T Mc M → ∀ K N : Subgroup G, NonBorelK T Mc M K N →
    (∀ L : Subgroup G, T ≤ L → L < K →
      oTwoUpper L ≤ Subgroup.centralizer (vE T Mc M : Set G)) →
    autOn (thompsonJi T 1) (V154 T Mc M) ≠ autOn T (V154 T Mc M) →
    ¬ Group.IsSolvable K → ¬ V154 T Mc M ≤ pCoreOf 2 K → V154 T Mc M ≤ pCoreOf 2 N

end CFSG.Quasithin.Gap6R2
