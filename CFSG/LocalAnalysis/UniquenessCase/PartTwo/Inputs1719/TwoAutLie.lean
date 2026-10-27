module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique (IsSylowTwoOf)

@[expose] def K_U4TwoAutPowerMap : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), IsU4 Y n → 1 < n →
    ∀ S : Subgroup Y, IsSylowTwoOf S ⊤ →
      ∀ α : MulAut Y, (∃ k : ℕ, α ^ 2 ^ k = 1) →
        S.map α.toMonoidHom = S →
          ∃ j : ℕ, ∀ x ∈ Subgroup.normalizer (S : Set Y),
            α x * (x ^ 2 ^ j)⁻¹ ∈ S

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
