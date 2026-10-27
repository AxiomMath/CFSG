module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811Centre
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K6aWeir
public import CFSG.GroupTheory.UniqueElemSylowTransfer
import CFSG.GroupTheory.WeirSylow.UniqueE27LinearFour
import CFSG.GroupTheory.WeirSylow.UniqueE27UnitaryFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.GroupTheory CFSG.Open Subgroup
open CFSG.GroupTheory.WeirSylow
  (uniqueElemSylow_of_statedClassicalModel_psl_four
   uniqueElemSylow_of_statedClassicalModel_psu_four)

theorem uniqueElemSylow_of_lieModel_l4 {X : Type} [Group X] {r f : ℕ}
    (h : IsLieFam811 X .l4 r f) : UniqueElemSylow 3 3 X := by
  obtain ⟨-, -, ⟨hmod, hM⟩ | ⟨hmod, hM⟩⟩ := h
  · exact uniqueElemSylow_of_statedClassicalModel_psl_four
      (hM.statedClassicalModel_of_ne_zero (by norm_num)) hmod
  · exact uniqueElemSylow_of_statedClassicalModel_psu_four
      (hM.statedClassicalModel_of_ne_zero (by norm_num)) hmod

theorem uniqueElemSylow_of_isLie811
    {Y : Type} [Group Y] [Finite Y] {fam : LieFam811} {r f : ℕ} (h : IsLie811 Y fam r f) :
    UniqueElemSylow 3 3 Y := by
  have hX : UniqueElemSylow 3 3 (Y ⧸ center Y) := by
    by_cases hfam : fam = .l4
    · subst hfam
      exact uniqueElemSylow_of_lieModel_l4 h.2.2
    · exact uniqueElemSylow_of_isLieFam811 h.2.2 hfam
  exact (UniqueElemSylow.quotient_iff (center Y) (not_three_dvd_card_center_of_isLie811 h)).1 hX

theorem k6a_holds :
    K6a := by
  intro Y _ _ fam r f h P
  exact uniqueElemSylow_of_isLie811 h P

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
