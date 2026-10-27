module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CharTwoTorusOn
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanRankFamilies
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L34OddCoverHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient)

section Certified


theorem k_BorelTorusAbelianRankTwoNotL34_of_griess
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess) :
    K_BorelTorusAbelianRankTwoNotL34 := by
  intro t m f ⟨hrk, hnot⟩ K _ _ hLM hq S hS
  have hadm := hLM.admissible
  have hcenter := k_BorelTorusAbelian_centerTwo_of_griess hN
  cases t with
  | PSL =>
    refine k_BorelTorusAbelian_PSL_of_cover_or_center hN hLM hq S hS ?_
    simp only [CFSG.Open.StatedLieAdmissible] at hadm
    obtain ⟨-, hf1, hm2, -, -⟩ := hadm
    simp only [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
    by_contra hbad
    push Not at hbad
    obtain ⟨hf3, hm2', hf1', h3m⟩ := hbad
    have hm : m = 3 := by omega
    have hf : f = 2 := by omega
    exact hnot ⟨rfl, hm, hf⟩
  | PSU =>
    refine k_BorelTorusAbelian_PSU_of_cover_or_gcd hN hLM hq S hS ?_
    simp only [CFSG.Open.StatedLieAdmissible] at hadm
    obtain ⟨-, hf1, hm3, hne⟩ := hadm
    simp only [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
    by_cases hf : 2 ≤ f
    · exact Or.inl hf
    · right
      obtain rfl : f = 1 := by omega
      have hm3' : m ≠ 3 := by
        rintro rfl
        exact hne rfl
      have hm : m = 4 ∨ m = 5 := by omega
      rcases hm with rfl | rfl <;> decide
  | PSp => exact k_BorelTorusAbelian_PSp hN K m f hadm hLM hq S hS
  | POmegaOdd => exact k_BorelTorusAbelian_POmegaOdd K m f hadm hLM hq S hS
  | POmegaPlus =>
    simp only [CFSG.Open.StatedLieAdmissible] at hadm
    simp only [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
    omega
  | POmegaMinus =>
    simp only [CFSG.Open.StatedLieAdmissible] at hadm
    simp only [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
    omega
  | G2 => exact k_BorelTorusAbelian_G2 hcenter K m f hadm hLM hq S hS
  | F4 => simp [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
  | E6 => simp [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
  | E7 => simp [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
  | E8 => simp [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
  | twistedE6 => simp [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
  | trialityD4 => exact k_BorelTorusAbelian_trialityD4 hcenter K m f hadm hLM hq S hS
  | twistedB2 => exact k_BorelTorusAbelian_twistedB2 hcenter K m f hadm hLM hq S hS
  | twistedG2 => exact k_BorelTorusAbelian_twistedG2 K m f hadm hLM hq S hS
  | twistedF4 => exact k_BorelTorusAbelian_twistedF4 hcenter K m f hadm hLM hq S hS
  | Tits => exact k_BorelTorusAbelian_Tits hN K m f hadm hLM hq S hS

theorem k_BorelTorusAbelianRankTwo_of_griess
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess) :
    K_BorelTorusAbelianRankTwo := by
  intro t m f hrk
  by_cases h34 : t = .PSL ∧ m = 3 ∧ f = 2
  · obtain ⟨rfl, rfl, rfl⟩ := h34
    intro K _ _ hLM hq S hS
    exact k_BorelTorusAbelian_PSL hN k_L34OddCover_holds K 3 2 hLM.admissible hLM hq S hS
  · exact k_BorelTorusAbelianRankTwoNotL34_of_griess hN t m f ⟨hrk, h34⟩

theorem k_BorelTorusAbelianRankThreeNotU62_of_griess
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess)
    (hΩ : K_BorelTorusAbelian_OmegaMinusEight) : K_BorelTorusAbelianRankThreeNotU62 := by
  intro t m f ⟨hrk, hnot⟩ K _ _ hLM hq S hS
  have hadm := hLM.admissible
  cases t with
  | PSL =>
    refine k_BorelTorusAbelian_PSL_of_cover_or_center hN hLM hq S hS
      (Or.inr (Or.inr (Or.inr ?_)))
    simp only [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
    simp only [CFSG.Open.StatedLieAdmissible] at hadm
    have hm : m = 4 := by omega
    subst hm
    omega
  | PSU =>
    refine k_BorelTorusAbelian_PSU_of_cover_or_gcd hN hLM hq S hS ?_
    simp only [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
    simp only [CFSG.Open.StatedLieAdmissible] at hadm
    by_cases hf : 2 ≤ f
    · exact Or.inl hf
    · right
      obtain rfl : f = 1 := by omega
      have hm : m = 7 := by
        have h67 : m = 6 ∨ m = 7 := by omega
        rcases h67 with rfl | rfl
        · exact absurd ⟨rfl, rfl, rfl⟩ hnot
        · rfl
      subst hm
      decide
  | PSp => exact k_BorelTorusAbelian_PSp hN K m f hadm hLM hq S hS
  | POmegaOdd => exact k_BorelTorusAbelian_POmegaOdd K m f hadm hLM hq S hS
  | POmegaPlus =>
    simp only [CFSG.Open.StatedLieAdmissible] at hadm
    simp only [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
    omega
  | POmegaMinus =>
    have hm : m = 4 := by
      simp only [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
      omega
    subst hm
    exact hΩ f K hLM hq S hS
  | G2 => simp [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
  | F4 => simp [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
  | E6 => simp [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
  | E7 => simp [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
  | E8 => simp [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
  | twistedE6 => simp [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
  | trialityD4 => simp [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
  | twistedB2 => simp [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
  | twistedG2 => simp [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
  | twistedF4 => simp [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk
  | Tits => simp [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk

theorem k_CartanRank_ne_twistedE6_of_griess
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess) :
    K_CartanRankOn fun t _ _ => t ≠ .twistedE6 := by
  intro t m f ht K _ _ hLM hq hodd S hS r hr hr2 hrd hPSL hE6
  have hadm := hLM.admissible
  cases t with
  | PSL => exact k_CartanRank_PSL_of_griess hN K m f hadm hLM hq hodd S hS r hr hr2 hrd hPSL hE6
  | PSU => exact k_CartanRank_PSU_holds K m f hadm hLM hq hodd S hS r hr hr2 hrd hPSL hE6
  | PSp => exact k_CartanRank_PSp_of_griess hN K m f hadm hLM hq hodd S hS r hr hr2 hrd hPSL hE6
  | POmegaOdd =>
    exact k_CartanRank_POmegaOdd_holds K m f hadm hLM hq hodd S hS r hr hr2 hrd hPSL hE6
  | POmegaPlus =>
    exact k_CartanRank_POmegaPlus_of_griess hN K m f hadm hLM hq hodd S hS r hr hr2 hrd hPSL hE6
  | POmegaMinus =>
    exact k_CartanRank_POmegaMinus_of_griess hN K m f hadm hLM hq hodd S hS r hr hr2 hrd hPSL hE6
  | G2 => exact k_CartanRank_G2_of_griess hN K m f hadm hLM hq hodd S hS r hr hr2 hrd hPSL hE6
  | F4 => exact k_CartanRank_F4_of_griess hN K m f hadm hLM hq hodd S hS r hr hr2 hrd hPSL hE6
  | E6 => exact k_CartanRank_E6_of_griess hN K m f hadm hLM hq hodd S hS r hr hr2 hrd hPSL hE6
  | E7 => exact k_CartanRank_E7_of_griess hN K m f hadm hLM hq hodd S hS r hr hr2 hrd hPSL hE6
  | E8 => exact k_CartanRank_E8_of_griess hN K m f hadm hLM hq hodd S hS r hr hr2 hrd hPSL hE6
  | twistedE6 => exact absurd rfl ht
  | trialityD4 =>
    exact k_CartanRank_trialityD4_of_griess hN K m f hadm hLM hq hodd S hS r hr hr2 hrd hPSL hE6
  | twistedB2 =>
    exact k_CartanRank_twistedB2_holds K m f hadm hLM hq hodd S hS r hr hr2 hrd hPSL hE6
  | twistedG2 =>
    exact k_CartanRank_twistedG2_holds K m f hadm hLM hq hodd S hS r hr hr2 hrd hPSL hE6
  | twistedF4 =>
    exact k_CartanRank_twistedF4_of_griess hN K m f hadm hLM hq hodd S hS r hr hr2 hrd hPSL hE6
  | Tits =>
    exact k_CartanRank_Tits_holds K m f hadm hLM hq hodd S hS r hr hr2 hrd hPSL hE6

theorem k_CartanRankLeThree_of_griess
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess) : K_CartanRankLeThree := by
  intro t m f hrk
  refine k_CartanRank_ne_twistedE6_of_griess hN t m f ?_
  rintro rfl
  simp [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] at hrk

end Certified

theorem k_BorelTorusAbelian_OmegaMinusEight_of_family (h : K_BorelTorusAbelian_POmegaMinus) :
    K_BorelTorusAbelian_OmegaMinusEight :=
  fun f K _ _ hLM hq S hS => h K 4 f hLM.admissible hLM hq S hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
