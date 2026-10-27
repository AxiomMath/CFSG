module

public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Quasithin.Background.F6Solvable

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def ComponentComparison15421 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I G₁ G₂ T₀ : Subgroup G),
    CFSG.SectionRank.IsSQTKCat ↥I →
    F6.IsGoldschmidtTripleIn I G₁ G₂ → G₁ ⊓ G₂ = T₀ →
    IsGoldschmidtAmalgam ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
      ((G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) →
    CharTwo I →
    ∀ hV : IsElemAbelian 2 (conjClosure (quasithinOmegaOneCenter T₀) I),
      I ⊓ Subgroup.centralizer (conjClosure (quasithinOmegaOneCenter T₀) I : Set G) =
        pCoreOf 2 I →
      IsFFModule (autI hV I) →
      (∃ K : Subgroup ↥(autI hV I), CFSG.IsComponent K) →
      ¬ IsPGroup 2 ↥(I ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T₀ : Set G))

end CFSG.Quasithin.EmptyFaithfulMultiple
