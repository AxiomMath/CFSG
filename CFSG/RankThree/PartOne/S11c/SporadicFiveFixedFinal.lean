module

public import CFSG.RankThree.PartOne.S11c.SporadicFiveFixedGroups
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneJ2
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneHSMcL
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneHe
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneRu
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneON
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneCo2
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneCo3
public import CFSG.RankThree.PartOne.KP.Fi22Section
public import CFSG.RankThree.PartOne.KS.FischerSections
public import CFSG.RankThree.PartOne.KP.BExclusion
public import CFSG.RankThree.PartOne.KP.MSectionMonster
public import CFSG.RankThree.PartOne.SPOR.Final

public section

namespace CFSG.RankThree.PartOne.HNRed

open CFSG CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.RankThree.Native
  CFSG.Sporadic.HeldB CFSG.Sporadic.RuSchreier CFSG.Sporadic.Co2Cert CFSG.Sporadic.Schreier.Co3
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem fiveFixedSporadicOnlyHN_of_co1_ly
    (hco1 : Co1FiveFixed) (hly : LyFiveFixed) : FiveFixedSporadicOnlyHN := by
  obtain ⟨h23, h24⟩ := sectionsForceEvenRankFour_fi23_fi24prime sectionsForceEvenRankFour_Fi22
    hasSection_fi23_fi22 hasSection_fi24prime_fi23
  exact fiveFixedSporadicOnlyHN_of_inputs
    { m11 := noFiveFixedPSU3_of_noPlaneAut noPlaneAut_M11
      m12 := noFiveFixedPSU3_of_noPlaneAut noPlaneAut_M12
      m22 := noFiveFixedPSU3_of_noPlaneAut noPlaneAut_M22
      m23 := noFiveFixedPSU3_of_noPlaneAut noPlaneAut_M23
      m24 := noFiveFixedPSU3_of_noPlaneAut noPlaneAut_M24
      j1 := noFiveFixedPSU3_of_noPlaneAut noPlaneAut_J1
      j2 := noFiveFixedPSU3_of_model j2_autModel j2_card_le j2PermEquiv (k := 4) (by norm_num)
        j2_two_part_le
      j3 := noFiveFixedPSU3_of_noPlaneAut noPlaneAut_J3
      j4 := noFiveFixedPSU3_J4
      hs := noFiveFixedPSU3_of_model hs_autModel hs_card_le hs100Equiv (k := 8) (by norm_num)
        hs_two_part_le
      mcl := noFiveFixedPSU3_of_model mcl_autModel mcl_card_le mcl275Equiv (k := 4) (by norm_num)
        mcl_two_part_le
      he := noFiveFixedPSU3_of_model heAutModel heAutGroup_card_le heEquivP (k := 8)
        (by norm_num) he_two_part_le_five
      ru := noFiveFixedPSU3_of_model ru_autModel (by omega) ruEquivP (k := 8) (by norm_num)
        ru_two_part_le
      suz := noFiveFixedPSU3_Suz
      on := noFiveFixedPSU3_of_not_sq_dvd fun _ _ _ _ hnab eT =>
        not_sq_dvd_card_mulAut_ONan hnab eT Nat.prime_five (by norm_num) (by norm_num)
      co1 := hco1
      co2 := noFiveFixedPSU3_of_model (co2_autModel SPOR.co2AllInner_holds) (by omega)
        co2PermEquiv (k := 8) (by norm_num) co2_two_part_le
      co3 := noFiveFixedPSU3_of_model (co3_autModel co3P_allInner) (by omega) co3PermEquiv
        (k := 4) (by norm_num) co3_two_part_le
      ly := hly
      th := noFiveFixedPSU3_Th
      fi22 := sectionsForceEvenRankFour_Fi22
      fi23 := h23
      fi24 := h24
      b := sectionsForceEvenRankFour_B
      m := simplePresentationM_sections_of_B_section sectionsForceEvenRankFour_B
        simplePresentationMHasBSection_holds }

end CFSG.RankThree.PartOne.HNRed
