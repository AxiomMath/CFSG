module

public import CFSG.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def SL3FourTorusFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L K : Subgroup G) (d : G), IsSL3 4 (O2Q X) →
    IsSylowTwoOf S X → L ≤ X → K ≤ X → S ≤ Subgroup.normalizer (L : Set G) →
    S ≤ Subgroup.normalizer (K : Set G) → ⁅L, L⁆ = L → ⁅K, K⁆ = K →
    Nonempty (O2Q L ≃* alternatingGroup (Fin 5)) → Nonempty (O2Q K ≃* alternatingGroup (Fin 5)) →
    ¬ K ≤ L ⊔ pCoreOf 2 X → d ∈ X → orderOf d = 3 →
    d ∈ Subgroup.normalizer (L : Set G) → d ∈ Subgroup.normalizer (K : Set G) →
    ⁅L, Subgroup.zpowers d⁆ ≤ pCoreOf 2 L → ⁅K, Subgroup.zpowers d⁆ ≤ pCoreOf 2 K

@[expose] def Sp4BlockParabolicFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L W : Subgroup G), IsSp4Block X →
    IsSylowTwoOf S X → L ≤ X → S ≤ Subgroup.normalizer (L : Set G) → ⁅L, L⁆ = L →
    Nonempty (O2Q L ≃* alternatingGroup (Fin 5)) → W ≤ X → IsPGroup 2 W →
    L ≤ Subgroup.normalizer (W : Set G) → Nat.card W ≤ 2 ^ 4 * Nat.card ↥(W ⊓ blockU X) →
      ⁅W, L⁆ ≤ blockU X

end CFSG.Quasithin.H13.Ch9
