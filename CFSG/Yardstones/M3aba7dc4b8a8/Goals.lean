module

public import CFSG.GF2Type.CenterFour.Assembly
public import CFSG.GF2Type.CenterFour.SettingBridge
public import CFSG.GF2Type.Aschbacher1976HigherCenter.Main
public import CFSG.GF2Type.Aschbacher1976HigherCenter.FourThree
public import CFSG.GF2Type.Smith1980Orth.OrthogonalCase
public import CFSG.GF2Type.SmithTypeE.GH74PartB
public import CFSG.GF2Type.SmithTypeE.YardstoneBridge
public import CFSG.GF2Type.Widths1112.Width12
public import CFSG.GF2Type.Widths1112.Width11
public import CFSG.GF2Type.Widths1112.Co2ModuleUniqueness
public import CFSG.GF2Type.Smith1979.W4AsLinMain
public import CFSG.GF2Type.Smith1979.W4AsSurvMain
public import CFSG.GF2Type.Smith1979.WidthSixCaseIII
public import CFSG.Quasithin.H13.AS91ResHolds823
public import CFSG.Quasithin.H13.AS91Sec8V1Holds
public import CFSG.GF2Type.SmithTypeE.E8.PartD

public section

namespace CFSG.Yardstones.M3aba7dc4b8a8

theorem aschbacher1976_center_four_case :
    Aschbacher1976CenterFourCase := by
  intro G _ _ _ z hset hnex hexp
  obtain ⟨n, hC⟩ := CFSG.GF2Type.CenterFour.exists_config hset hnex hexp
  exact hC.false.elim

theorem aschbacher1976_higher_center_case :
    Aschbacher1976HigherCenterCase :=
  CFSG.GF2Type.Aschbacher1976HigherCenter.higher_center_case_of_four_three
    CFSG.GF2Type.Aschbacher1976HigherCenter.cyclicFourNotWeaklyClosed

theorem width_four_weakly_closed_case :
    WidthFourWeaklyClosedCase := by
  intro G _ _ _ z hset hext hcard hwc
  rcases CFSG.GF2Type.aschbacherFSmith1977Statement_holds G hset.1 z hset.2.2.2.2.1 hext 4
    (by rw [hcard]) (by norm_num) hwc with h | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

theorem width_four_reducible_case :
    WidthFourReducibleCase := by
  intro G _ _ _ z hset hext hcard hwc hred
  exact (CFSG.LargeExtraspecial.DW.W4Rank.false_of_width_four_reducible_of_theoremA
    CFSG.LargeExtraspecial.DW.W4Rank.theoremAWidthFour_holds hset hext hcard hwc hred).elim

theorem width_four_irreducible_case :
    WidthFourIrreducibleCase :=
  CFSG.GF2Type.Smith1979.W4As.widthFourIrreducibleCase_of_layerSurvivors
    CFSG.GF2Type.Smith1979.W4As.layerSurvivorsW4_holds

theorem width_six_alternative_four_case :
    WidthSixAlternativeFourCase :=
  CFSG.GF2Type.Smith1979.widthSixAlternativeFourCase_of_parrott
    (CFSG.Quasithin.H13.AS91.inputAS91_of_stmt8_2_3 CFSG.Quasithin.H13.AS91.stmt8_2_3_holds)

theorem orthogonal_case :
    OrthogonalCase :=
  CFSG.GF2Type.Smith1980Orth.orthogonalCase_of_six
    CFSG.GF2Type.Smith1980Orth.smith1980OrthogonalSix_holds

theorem width_ten_e6_case :
    WidthTenE6Case :=
  CFSG.GF2Type.SmithTypeE.widthTenE6Case_of_parts
    (CFSG.GF2Type.SmithTypeE.partA_partB_of_gh74
      CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models).1
    (CFSG.GF2Type.SmithTypeE.partA_partB_of_gh74
      CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models).2

theorem widths_sixteen_twenty_eight_case :
    WidthsSixteenTwentyEightCase :=
  CFSG.GF2Type.SmithTypeE.widthsSixteenTwentyEightCase_of_parts
    (CFSG.GF2Type.SmithTypeE.partC_of_gh74_only
      CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models)
    (CFSG.GF2Type.SmithTypeE.partD_of_gh74
      CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models)

theorem width_eleven_co2_case :
    WidthElevenCo2Case := by
  intro G _ _ _ z hset hext hcard Mbar _ hMbar hCo2
  exact (CFSG.GF2Type.Widths1112.widthEleven_false
    CFSG.GF2Type.Widths1112.co2ModuleUniqueness_holds
    CFSG.LargeExtraspecial.S14.aschbacherSmith35Input_holds hset.2.2.1
    hset.2.2.2.2.1 hext hcard hMbar hCo2).elim

theorem width_twelve_co1_case :
    WidthTwelveCo1Case := by
  intro G _ _ _ z hset hext hcard Mbar _ hMbar hCo1
  exact (CFSG.GF2Type.Widths1112.widthTwelve_false
    CFSG.LargeExtraspecial.S14.aschbacherSmith35Input_holds hset.2.2.1
    hset.2.2.2.2.1 hext hcard hMbar hCo1).elim

end CFSG.Yardstones.M3aba7dc4b8a8
