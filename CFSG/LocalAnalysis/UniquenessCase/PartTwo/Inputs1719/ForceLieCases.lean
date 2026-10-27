module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCatTypeDet
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.G2EvenOuterTypeDet

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Blueprint CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19


theorem forceLie_cases {Q : Type} [Group Q] (hL : IsLieTypeOver2 Q) (hlist : List19_16_5 Q) :
    LieModel Q .PSL 3 2 1 ∨ LieModel Q .PSL 4 2 1 ∨ LieModel Q .PSL 5 2 1 ∨
      LieModel Q .PSL 6 2 1 ∨ LieModel Q .PSL 7 2 1 ∨ LieModel Q .PSU 4 2 1 ∨
      LieModel Q .PSp 3 2 1 ∨ LieModel Q .POmegaMinus 4 2 1 ∨ IsAlt Q 6 ∨
      LieModel Q .PSU 3 3 1 := by
  rcases hL with ⟨t, m, hadm, hQ⟩ | hA | hU
  · rcases hlist with (⟨m', hG | h3 | hS4 | hU4 | h4 | hS6 | hO⟩ | ⟨s, hs5, hs7, hs⟩) |
      hA | hU | hU5
    · obtain ⟨-, h1⟩ := CFSG.EvenSporadicStandard.Induction.lieModel_G2_two_unique hG hQ
      subst h1
      exact absurd (LieModel.admissible (hG : LieModel Q .G2 0 2 1)).2.2.2 (by norm_num)
    · obtain ⟨-, -, h1⟩ :=
        CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique (by norm_num) h3 hQ
      subst h1
      exact Or.inl h3
    · obtain ⟨-, -, h1⟩ := CFSG.SeitzReduction.SymplecticPilot.lieModel_PSp_two_unique hS4 hQ
      subst h1
      exact (CFSG.SeitzReduction.SymplecticPilot.not_lieModel_PSp_two_two_one hS4).elim
    · obtain ⟨-, -, h1⟩ :=
        CFSG.SeitzReduction.UnitaryPilot.sumEvenTypeDetAt le_rfl Q m' t m 1 hU4 hadm hQ
      subst h1
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hU4)))))
    · obtain ⟨-, -, h1⟩ :=
        CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique (by norm_num) h4 hQ
      subst h1
      exact Or.inr (Or.inl h4)
    · obtain ⟨-, -, h1⟩ := CFSG.SeitzReduction.SymplecticPilot.lieModel_PSp_two_unique hS6 hQ
      subst h1
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hS6))))))
    · obtain ⟨-, -, h1⟩ :=
        CFSG.SeitzReduction.TwistedE6Pilot.lieModel_POmegaMinus_four_two_unique hO hQ
      subst h1
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hO)))))))
    · interval_cases s
      · exact Or.inr (Or.inr (Or.inl hs))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hs)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hA))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hU))))))))
    · obtain ⟨-, -, h1⟩ :=
        CFSG.SeitzReduction.UnitaryPilot.sumEvenTypeDetAt (by norm_num) Q 2 t m 1 hU5 hadm hQ
      exact absurd h1 (by norm_num)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hA))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hU))))))))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
