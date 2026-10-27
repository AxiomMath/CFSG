module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.KInputsLie
import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalCoords
import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalSevenCent
import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalSevenPoints
import CFSG.GroupTheory.WeirSylow.UniqueE27Linear
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811Centre
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811ModelTransport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811ModelUnpack

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open Subgroup CFSG.ClassicalGroups
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (qPlusPi)

theorem k7L7TwoMech_holds :
    K7L7TwoMech := by
  intro Y _ _ h A hA h27
  have hZ1 : Nat.card (center Y) ∣ 1 := by
    have h1 : Nat.gcd 7 (qPlusPi 2 1) = 1 := by decide
    rw [← h1]
    exact Theorem82.card_center_dvd_of_isLie811_l7 h
  have hZ3 : ¬ 3 ∣ Nat.card (center Y) := fun h3 => by
    have := Nat.le_of_dvd one_pos (h3.trans hZ1)
    omega
  have hZ7 : ¬ 7 ∣ Nat.card (center Y) := fun h7 => by
    have := Nat.le_of_dvd one_pos (h7.trans hZ1)
    omega
  obtain ⟨-, -, -, hm⟩ := h
  rcases hm with ⟨-, hLM⟩ | ⟨h1, -⟩
  swap
  · exact absurd h1 (by decide)
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ :=
    Theorem82.ModelUnpack.exists_model_of_lieModel_psl (by norm_num) hLM
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  have hK3 : Nat.card K % 3 = 2 := by rw [hK2]
  have h₀ := SLnThreeLocal.c₀_signedCoords (SLnThreeLocal.three_ne_zero_of_natCard_mod_three hK3)
    (Or.inr rfl : 7 = 6 ∨ 7 = 7)
  have hU := CFSG.GroupTheory.WeirSylow.uniqueElemSylow_statedProj_statedSL_of_mod_three_eq_two K
    hK3 (Or.inr rfl : 7 = 6 ∨ 7 = 7)
  have hN3 : ¬ 3 ∣ Nat.card ((StatedScalars (Fin 7) K).subgroupOf (StatedSL 7 K)) :=
    Theorem82.ModelUnpack.not_dvd_card_scalars_of_not_dvd_card_sub_one Nat.prime_three
      (by rw [hK2]; norm_num) _
  have hN7 : ¬ 7 ∣ Nat.card ((StatedScalars (Fin 7) K).subgroupOf (StatedSL 7 K)) :=
    Theorem82.ModelUnpack.not_dvd_card_scalars_of_not_dvd_card_sub_one (by norm_num)
      (by rw [hK2]; norm_num) _
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact ⟨Theorem82.ModelTransport.not_dvd_card_centralizer_of_model hU hN3 hZ3 hN7 hZ7 e
      h₀.isElemAbelian h₀.card_eq (SLnThreeLocal.not_seven_dvd_card_centralizer_range_c₀ hK2)
      hA h27,
    Theorem82.ModelTransport.dvd_card_centralizer_points_of_model h₀ hN3 hU hZ3 hN7 hZ7 e
      (SLnThreeLocal.seven_dvd_card_centralizer_c₀_weight_one hK2)
      (SLnThreeLocal.seven_dvd_card_centralizer_c₀_weight_two hK2)
      (SLnThreeLocal.seven_dvd_card_centralizer_c₀_weight_three hK2) hA h27⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
