module

public import CFSG.Quasithin.Vol2.Ch6StatementsSec2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

@[expose] def Res624Six : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G), Hyp6Sec2 G T M L V →
    ∀ U : Subgroup G, U ≤ V → mQuot V U = 2 →
    ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) →
    IsSylowIn 2 (T ⊓ Subgroup.normalizer (U : Set G)) (M ⊓ Subgroup.normalizer (U : Set G)) →
      QuasithinUnique.CharTwo (Subgroup.centralizer (U : Set G)) →
      Nat.card ↥(oTwoUpper (L ⊓ Subgroup.normalizer (U : Set G))) =
        3 * Nat.card ↥(pCoreOf 2 (oTwoUpper (L ⊓ Subgroup.normalizer (U : Set G)))) →
      pCoreOf 2 (oTwoUpper (L ⊓ Subgroup.normalizer (U : Set G))) =
        oTwoUpper (L ⊓ Subgroup.normalizer (U : Set G)) ⊓ Subgroup.centralizer (U : Set G) →
      ∀ K K' : Subgroup G, quasithinIsCComponent K (Subgroup.centralizer (U : Set G)) →
        quasithinIsCComponent K' (Subgroup.centralizer (U : Set G)) →
        3 ∣ Nat.card K → 3 ∣ Nat.card K' → K = K'

end CFSG.Quasithin.H13
