module

public import CFSG.Quasithin.Background.B69Asm

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace B69

@[expose] def AsB69AltBlock : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X T M A L : Subgroup (MulAut V)), CompHyp X T M A L →
      ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) → AltShape M A L W →
        ∀ A' : Subgroup (MulAut V), IsFFStarMin X A' → ⁅L, A'⁆ = L → A' ≤ L ⊔ A

@[expose] def AsB69GenByMin : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X T M : Subgroup (MulAut V)),
      (∃ (H : Type) (_ : Group H) (_ : Finite H), CFSG.Open.SQTKTauCeti.StronglyQuasithin H ∧
        CFSG.SectionRank.IsKGroupCat H ∧ ∃ f : H →* ↥X, Function.Surjective f) →
      MinParabolic X T M → pCoreOf 2 X = ⊥ → IsFFModule X → ¬ Group.IsSolvable ↥X →
      ffJ X ≤ ffJP {A | IsFFStarMin X A} X

end B69

end CFSG.Quasithin
