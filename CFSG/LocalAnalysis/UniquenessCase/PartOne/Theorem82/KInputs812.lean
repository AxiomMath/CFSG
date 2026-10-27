module

public import CFSG.Open.Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

@[expose] def OuterThreeSplit : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → CFSG.Open.IsQuasisimple X →
    ¬ 3 ∣ Nat.card (Subgroup.center X) → CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1 →
    ∀ R S : Subgroup (MulAut X), IsPGroup 3 R →
      CFSG.ABGLocalTools.IsSylowOf 3 S (MulAut.conj : X →* MulAut X).range → S ≤ R →
      ∀ α ∈ R, α ^ 3 ∈ S → ∃ s ∈ S, (s * α) ^ 3 = 1

@[expose] def PerfectAutInner : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → CFSG.Open.IsQuasisimple X →
    ¬ 3 ∣ Nat.card (Subgroup.center X) → CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1 →
    ∀ Y : Subgroup (MulAut X), ⁅Y, Y⁆ = Y → Y ≤ (MulAut.conj : X →* MulAut X).range

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
