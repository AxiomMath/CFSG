module

public import CFSG.RankThree.PartTwo.Setup

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.Assembly.RankThreeEven (projSU)

@[expose] def OutFixCentralThreeAbelian46Rank : Prop :=
  ∀ (X : Type) [Group X] [Finite X], SectionFourHyp X → CFSG.IsQuasisimple X →
    CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3 →
    ∀ z ∈ Subgroup.center X, orderOf z = 3 →
    ∀ σ τ : MulAut X, σ z = z → τ z = z →
      σ * τ * σ⁻¹ * τ⁻¹ ∈ (MulAut.conj : X →* MulAut X).range

end CFSG.RankThree.PartTwo.KFacts
