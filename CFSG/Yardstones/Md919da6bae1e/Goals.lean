module

public import CFSG.Yardstones.Md919da6bae1e.Definitions
public import CFSG.Yardstones.M59c2a5af36f1.Goals
public import CFSG.Yardstones.Mf4cdcdf2e013.Goals
public import CFSG.RankThree.PartTwo.Sec20.SimsItem201Of310
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aItems
public import CFSG.RankThree.PartTwo.Sec19.Ronan1914From310
import CFSG.RankThree.PartTwo.Sec21.RonanYS15
public import CFSG.RankThree.PartTwo.Sec21.LitScopeProofGL83

public section

namespace CFSG.Yardstones.Md919da6bae1e

theorem ys01_gf2TypeE27 :
    CFSG.RankThree.PartTwo.Sec6.GF2TypeE27 :=
  CFSG.RankThree.PartTwo.Sec6.gf2TypeE27_of_inputs''
    CFSG.GF2Type.Aschbacher1976Full.aschbacher1976Statement_holds
    CFSG.Yardstones.M59c2a5af36f1.smith_1979

theorem ys02_item4_34Sec :
    CFSG.RankThree.PartTwo.Sec4.Item4_34Sec :=
  CFSG.RankThree.PartTwo.Sec4.item4_34Sec_of_leaves CFSG.RankThree.PartTwo.Sec19.seitzThreeTrialityWideTwo_holds CFSG.RankThree.PartTwo.Sec19.seitzExcAnisotropicTrialityThreeTwo_holds
    (CFSG.RankThree.PartTwo.Sec4.E27.seitz434RestTwentySeven_of_rows CFSG.RankThree.PartTwo.Sec4.E27.seitz27L3F_holds CFSG.RankThree.PartTwo.Sec4.E27.seitz27_trialityD4_final_layer)
    (CFSG.RankThree.PartTwo.Sec4.E27.seitz434OtherTwentySeven_of_rows CFSG.RankThree.PartTwo.Sec4.E27.seitz27_trialityD4_final_layer
      CFSG.RankThree.PartTwo.Sec4.E27.reeF4EightFixPlaneGen_of_certs)

theorem ys03_item4_44_3Diag :
    CFSG.RankThree.PartTwo.Sec4.Item4_44_3Diag :=
  CFSG.RankThree.PartTwo.Sec4.item4_44_3Diag_of_item434Sec
    (CFSG.RankThree.PartTwo.Sec4.item4_34Sec_of_leaves CFSG.RankThree.PartTwo.Sec19.seitzThreeTrialityWideTwo_holds CFSG.RankThree.PartTwo.Sec19.seitzExcAnisotropicTrialityThreeTwo_holds
    (CFSG.RankThree.PartTwo.Sec4.E27.seitz434RestTwentySeven_of_rows CFSG.RankThree.PartTwo.Sec4.E27.seitz27L3F_holds CFSG.RankThree.PartTwo.Sec4.E27.seitz27_trialityD4_final_layer)
    (CFSG.RankThree.PartTwo.Sec4.E27.seitz434OtherTwentySeven_of_rows CFSG.RankThree.PartTwo.Sec4.E27.seitz27_trialityD4_final_layer
      CFSG.RankThree.PartTwo.Sec4.E27.reeF4EightFixPlaneGen_of_certs))

theorem ys04_item612
    : CFSG.RankThree.PartTwo.Sec21.Item612 :=
  CFSG.RankThree.PartTwo.Sec6.rank3II_6_12_sec21_closed

theorem ys05_item128BarAt
    : CFSG.RankThree.PartTwo.Sec12.Item128BarAt :=
  CFSG.RankThree.PartTwo.Sec12.item128BarAt_of_inputs
    (CFSG.RankThree.PartTwo.Sec11.item1134E27N_of
      CFSG.RankThree.PartTwo.Sec11.Close.narrow_sec9Hyp91SmallNever)

theorem ys06_item131
    : CFSG.RankThree.PartTwo.Sec13.Item131 :=
  CFSG.RankThree.PartTwo.Sec13.rank3II_13_1_holds

theorem ys07_item1730
    : CFSG.RankThree.PartTwo.Sec17.Item1730 :=
  CFSG.RankThree.PartTwo.Sec17.item1730_of_gf2n CFSG.Yardstones.Mf4cdcdf2e013.gf2n_type_statement

theorem ys08_item194UsedWide3
    : CFSG.RankThree.PartTwo.Sec19.Item194UsedWide3 :=
  CFSG.RankThree.PartTwo.Sec19.item194UsedWide3_of_item316
    (CFSG.RankThree.PartTwo.Sec19.item316_of_gf2n CFSG.Yardstones.Mf4cdcdf2e013.gf2n_type_statement)

theorem ys09_item195
    : CFSG.RankThree.PartTwo.Sec19.Item195 :=
  have h434 : CFSG.RankThree.PartTwo.Sec4.Item4_34Sec := ys02_item4_34Sec
  have h45 := CFSG.RankThree.PartTwo.Sec4.rank3II_4_5
  have hspor := CFSG.RankThree.PartTwo.Sec13.sporadicModels131
  have h4441 := CFSG.RankThree.PartTwo.Sec4.rank3II_4_44_1_of_item4_34 h434 h45
  have h4442 := CFSG.RankThree.PartTwo.Sec4.rank3II_4_44_2_of h45 h434
  have h198 := CFSG.RankThree.PartTwo.Sec19.step198_of ys06_item131 hspor h45
    (CFSG.RankThree.PartTwo.Sec4.rank3II_4_8_of h45) CFSG.RankThree.PartTwo.Sec19.census198_holds
  have h1910 := CFSG.RankThree.PartTwo.Sec19.step1910_of_wide3 ys08_item194UsedWide3
  have h1911 := CFSG.RankThree.PartTwo.Sec19.step1911_of_wide3 ys08_item194UsedWide3
  have h1911E :=
    CFSG.RankThree.PartTwo.Sec19.step1911End_of_wide3 ys08_item194UsedWide3 ys06_item131
  have h197 := CFSG.RankThree.PartTwo.Sec19.step197_of h4441 h4442 h45 ys06_item131
    ys07_item1730 hspor h198 h1910 h1911 h1911E
  CFSG.RankThree.PartTwo.Sec19.rank3II_19_5_of ys07_item1730 ys06_item131 hspor
    (CFSG.RankThree.PartTwo.Sec18.rank3II_18_1_1_of h4441)
    (CFSG.RankThree.PartTwo.Sec18.rank3II_18_1_2_of h4442
      CFSG.RankThree.PartTwo.KFacts.KS18.ks18OuterInvolution)
    (CFSG.RankThree.PartTwo.Sec19.step196_of h45 ys06_item131 hspor) h198
    (CFSG.RankThree.PartTwo.Sec19.step198D_of h197)
    (CFSG.RankThree.PartTwo.Sec19.step199_of h197 h198
      CFSG.RankThree.PartTwo.Sec19.RonanSeitz199.seitz199_holds)
    (CFSG.RankThree.PartTwo.Sec19.rank3II_19_10_O2_of_spor ys06_item131 hspor) h1910 h1911 h1911E

theorem ys10_step1914
    : CFSG.RankThree.PartTwo.Sec19.Step1914 :=
  CFSG.RankThree.PartTwo.Sec19.Ronan1914.step1914_of_310
    (CFSG.RankThree.GF2n.item3_10_of_gf2nTypeStatement
      CFSG.Yardstones.Mf4cdcdf2e013.gf2n_type_statement)

theorem ys11_steps1918Core1919
    : CFSG.Yardstones.Md919da6bae1e.Steps1918Core1919 :=
  ⟨CFSG.RankThree.PartTwo.Sec19.Ronan1914.step1918_of_310
      (CFSG.RankThree.GF2n.item3_10_of_gf2nTypeStatement
        CFSG.Yardstones.Mf4cdcdf2e013.gf2n_type_statement),
    CFSG.RankThree.PartTwo.Sec19.Ronan825Y.step1919CoreSplitLie_holds⟩

theorem ys12_item201Contra1
    : CFSG.RankThree.PartTwo.Sec20.Item201Contra1 :=
  CFSG.RankThree.PartTwo.Sec20.item201Contra1_of_gf2n
    CFSG.Yardstones.Mf4cdcdf2e013.gf2n_type_statement

theorem ys13_item231
    : CFSG.RankThree.PartTwo.Sec21.Item231 :=
  CFSG.RankThree.PartTwo.Sec21.FF81.item231_of_gf2n
    CFSG.Yardstones.Mf4cdcdf2e013.gf2n_type_statement

theorem ys14_item233
    : CFSG.RankThree.PartTwo.Sec21.Item233 :=
  CFSG.RankThree.PartTwo.Sec21.FF81.item233_of_gf2n
    CFSG.Yardstones.Mf4cdcdf2e013.gf2n_type_statement

theorem ys15_gl83StronglyEmbeddedNoSimpleThree :
    CFSG.RankThree.PartTwo.Sec21.GL83StronglyEmbeddedNoSimpleThree :=
  CFSG.RankThree.PartTwo.Sec21.RonanYS15.gl83StronglyEmbeddedNoSimpleThree_holds

end CFSG.Yardstones.Md919da6bae1e
