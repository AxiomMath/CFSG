module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CharacterTheory.Semidihedral.Principal.FreeSixCharacterDefectFourSupport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient)

@[expose] def K_U5TorusRank : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (f : ℕ),
    CFSG.Open.StatedLieAdmissible .PSU 5 2 f →
    LieModel (K ⧸ Subgroup.center K) .PSU 5 2 f →
    CFSG.Open.IsQuasisimple K →
    ∀ S : Subgroup K, IsSylowTwoOf S ⊤ →
      ∀ s : ℕ, s.Prime → s ∣ 2 ^ f + 1 →
        ¬ (s = 5 ∧ Nat.card (Subgroup.center K) = 1 ∧ ¬ 25 ∣ 2 ^ f + 1) →
          2 ≤ CFSG.Open.pRank s (⊤ : Subgroup (normalizerQuotient S))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
