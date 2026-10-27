module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_ONanQuotThreeRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSpor X .ONan →
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)

@[expose] def K_M22OddCover : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    CFSG.Open.IsQuasisimple X → Odd (Nat.card (Subgroup.center X)) →
      IsSpor (X ⧸ Subgroup.center X) .M22 →
        ¬ IsSpor X .J2 ∧ (Subgroup.center X = ⊥ ∨ Nat.card (Subgroup.center X) = 3)

@[expose] def K_SporadicThreePermuting : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y) (s : TauCeti.SporadicName),
    K.Normal →
    CFSG.Open.IsQuasisimple ↥K →
    Odd (Nat.card (Subgroup.center ↥K)) →
    IsSpor (↥K ⧸ Subgroup.center ↥K) s →
    Subgroup.centralizer (K : Set Y) = (Subgroup.center ↥K).map K.subtype →
    (∃ n : ℕ, K.index = 2 ^ n) →
    CFSG.Quasithin.IsSylowIn 2 S ⊤ →
    2 < CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) → s ≠ .ONan →
      ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
        ¬ IsCyclic ↥E ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
