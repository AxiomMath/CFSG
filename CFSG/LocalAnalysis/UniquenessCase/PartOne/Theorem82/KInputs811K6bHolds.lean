module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811Centre

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K6aHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K6bHeavy
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K6bLight
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

theorem three_le_pRank_centralizer_of_isLie811
    {Y : Type} [Group Y] [Finite Y] {fam : LieFam811} {r f : ℕ} (h : IsLie811 Y fam r f)
    {x : Y} (hx : orderOf x = 3) :
    3 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer {x}) := by
  have hZ := not_three_dvd_card_center_of_isLie811 h
  rcases fam with _ | _ | _ | _ | _ | _
  · exact three_le_pRank_centralizer_of_isLie811_light h hZ (Or.inl rfl) hx
  · exact three_le_pRank_centralizer_of_isLie811_light h hZ (Or.inr (Or.inl rfl)) hx
  · exact three_le_pRank_centralizer_of_isLie811_heavy h hZ (Or.inr (Or.inr rfl)) hx
  · rcases pow_mod_three_cases_of_isLie811 h (Or.inl rfl) with h1 | h2
    · exact three_le_pRank_centralizer_of_isLie811_light h hZ
        (Or.inr (Or.inr (Or.inl ⟨rfl, h1⟩))) hx
    · exact three_le_pRank_centralizer_of_isLie811_heavy h hZ (Or.inl ⟨rfl, h2⟩) hx
  · rcases pow_mod_three_cases_of_isLie811 h (Or.inr (Or.inl rfl)) with h1 | h2
    · exact three_le_pRank_centralizer_of_isLie811_heavy h hZ
        (Or.inr (Or.inl ⟨Or.inl rfl, h1⟩)) hx
    · exact three_le_pRank_centralizer_of_isLie811_light h hZ
        (Or.inr (Or.inr (Or.inr ⟨Or.inl rfl, h2⟩))) hx
  · rcases pow_mod_three_cases_of_isLie811 h (Or.inr (Or.inr rfl)) with h1 | h2
    · exact three_le_pRank_centralizer_of_isLie811_heavy h hZ
        (Or.inr (Or.inl ⟨Or.inr rfl, h1⟩)) hx
    · exact three_le_pRank_centralizer_of_isLie811_light h hZ
        (Or.inr (Or.inr (Or.inr ⟨Or.inr rfl, h2⟩))) hx

theorem k6b_of_k6a
    (h6a : K6a) : K6b := by
  intro Y _ _ fam r f h A hA hAc x hx
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU : CFSG.GroupTheory.UniqueElemSylow 3 3 Y := fun P => by
    simpa using h6a Y fam r f h P
  exact CFSG.GroupTheory.UniqueElemSylow.exists_conj_mem (by norm_num) hU
    (fun y hy => three_le_pRank_centralizer_of_isLie811 h hy) hA (by simpa using hAc) hx

theorem k6b_holds :
    K6b :=
  k6b_of_k6a k6a_holds

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
