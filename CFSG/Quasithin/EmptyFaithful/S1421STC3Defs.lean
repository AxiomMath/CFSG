module

public import CFSG.Quasithin.EmptyFaithful.S1421Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Lemma14209Used : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    S1421.sOf T K1 < T →
    ∃ Kc ∈ cComp (mcOf T), K1 ≤ Kc ∧ oTwoUpper H ≤ Kc ⊔ T ∧
      ∀ T1 : Subgroup G, IsSylowTwoOf T1 (mcOf T) → S1421.sOf T K1 ≤ T1 →
        Kc ≤ K1 ⊔ T1 ∨ 2 ≤ CFSG.Open.pRank 3 (conjClosure K1 T1)

@[expose] def Lemma14210 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    S1421.sOf T K1 < T → ∀ T1 : Subgroup G, IsSylowTwoOf T1 (mcOf T) → S1421.sOf T K1 ≤ T1 →
      IsUniqueM (K1 ⊔ T1) (mcOf T)

end CFSG.Quasithin
