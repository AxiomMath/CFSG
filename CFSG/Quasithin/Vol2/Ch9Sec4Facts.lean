module

public import CFSG.Quasithin.Vol2.Ch5StatementsB
public import CFSG.Quasithin.Vol2.Ch1ModO2

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def A314QuasiRankFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y T B L E : Subgroup G), SQTKGroup ↥Y →
    pCoreOf 2 Y ≠ ⊥ → IsSylowTwoOf T Y → B ∈ lFamily T → T ≤ Subgroup.normalizer (B : Set G) →
    Nonempty (O2Q B ≃* alternatingGroup (Fin 5)) → L ∈ cComp Y → B < L →
    A314Statement (o2Img Y T) (modO2Image Y B) (modO2Image Y L) → CFSG.IsQuasisimple ↥L →
    E ≤ Subgroup.normalizer (L : Set G) → IsElemAbelian 2 E →
    E ⊓ Subgroup.centralizer (L : Set G) ≤ L → E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ →
      rk ↥E ≤ 7

@[expose] def A314FFCohomFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y T K KY U U₀ : Subgroup G) (v : G), SQTKGroup ↥Y →
    IsSylowTwoOf T Y → K ≤ Y → K ∈ lFamily T → T ≤ Subgroup.normalizer (K : Set G) →
    Nonempty (O2Q K ≃* alternatingGroup (Fin 5)) → KY ∈ cComp Y → K < KY →
    Y ≤ Subgroup.normalizer (KY : Set G) → IsTwoReducedIn Y U →
    ¬ ⁅KY, thompsonJ T⁆ ≤ Subgroup.centralizer (U : Set G) →
    ¬ KY ≤ K ⊔ (KY ⊓ Subgroup.centralizer (U : Set G)) →
    U₀ ≤ U → U₀ ≤ ⁅U₀, K⁆ → pCoreOf 2 K ≤ Subgroup.centralizer (U₀ : Set G) →
    v ∈ U₀ → v ≠ 1 → KY ≤ Subgroup.centralizer ({v} : Set G) → False

end CFSG.Quasithin.H13.Ch9
