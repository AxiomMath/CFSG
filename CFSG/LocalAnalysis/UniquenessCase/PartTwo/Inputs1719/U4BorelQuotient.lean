module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CharacterTheory.Semidihedral.Principal.FreeSixCharacterDefectFourSupport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def KU4U5CartanQuotient : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), 2 ≤ n → Even n →
    ((∃ n' : ℕ, IsU4 Y n' ∧ n' = n) ∨ IsU5 Y 2) →
      ∀ S : Sylow 2 Y,
        IsMulCommutative (TauCeti.Subgroup.normalizerQuotient (S : Subgroup Y)) ∧
          ∃ E : Subgroup (TauCeti.Subgroup.normalizerQuotient (S : Subgroup Y)),
            IsElemAbelian 3 E ∧ Nat.card E = 9

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
