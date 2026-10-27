module

import CFSG.HardMathSupport.Curtis.Coordinator.ToralThreeReduce
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII
import CFSG.Quasithin.Background.A318POutSpor
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (IsA6Z3 IsA7Z3 IsM22Z3)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem not_three_dvd_card_outer_of_cover
    {X : Type} [Group X] [Finite X] (h : IsA6Z3 X ∨ IsA7Z3 X ∨ IsM22Z3 X) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  rcases h with hA6 | hA7 | hM22
  · obtain ⟨hqs, -, hAlt⟩ := hA6
    obtain ⟨e⟩ := hAlt
    have : Group.IsPerfect X := hqs.1
    have : IsSimpleGroup (X ⧸ Subgroup.center X) := hqs.2.1
    exact CFSG.HardMathSupport.Curtis.Coordinator.not_three_dvd_card_outer_of_center_alt e
  · obtain ⟨hqs, -, hAlt⟩ := hA7
    obtain ⟨e⟩ := hAlt
    have : Group.IsPerfect X := hqs.1
    have : IsSimpleGroup (X ⧸ Subgroup.center X) := hqs.2.1
    exact CFSG.HardMathSupport.Curtis.Coordinator.not_three_dvd_card_outer_of_center_alt e
  · obtain ⟨hqs, -, hSpor⟩ := hM22
    obtain ⟨e⟩ := hSpor
    have : Group.IsPerfect X := hqs.1
    intro hdiv
    exact CFSG.Quasithin.A318P.not_dvd_outer_M22 e Nat.prime_three (by norm_num)
      (dvd_trans hdiv (CFSG.AGLEmbedding.card_outer_dvd_card_outer_centerQuotient X))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
