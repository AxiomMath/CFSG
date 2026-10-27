module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def RadicalSzComponent : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (U : Subgroup S) (n : ℕ), IsSimpleGroup S →
    CFSG.Blueprint.EvenLieType S → U ≠ ⊥ → IsPGroup 2 U →
    CFSG.Open.pCoreOf 2 (normalizer (U : Set S)) = U →
    (∃ B : Subgroup (↥(normalizer (U : Set S)) ⧸ CFSG.pCore 2 ↥(normalizer (U : Set S))),
      CFSG.Open.IsComponentOf B ⊤ ∧ IsSz ↥B n) →
    CFSG.Blueprint.LieModel S .twistedF4 0 2 n

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
