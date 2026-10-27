module

public import CFSG.RankThree.PartTwo.Sec21.FF84Closed
public import CFSG.RankThree.PartTwo.Sec21.FF84Chain
public import CFSG.RankThree.PartTwo.Sec21.FF84S36Assemble
public import CFSG.RankThree.PartTwo.Sec21.FF84S4APiStar
public import CFSG.RankThree.PartTwo.Sec21.FF84S410Data
public import CFSG.RankThree.PartTwo.Sec21.FF84S411Main
public import CFSG.RankThree.PartTwo.Sec21.FF84S411Transv
public import CFSG.RankThree.PartTwo.Sec21.FF84S411NoAltOm
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmHolds
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmA4Final
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmA4Sec3AS4
public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOPHolds
public import CFSG.RankThree.PartTwo.Sec21.FF79KLemmaOExcHolds
public import CFSG.RankThree.PartTwo.Sec21.FF84S3A9
public import CFSG.RankThree.PartTwo.Sec21.FF84S4AUMax
public import CFSG.RankThree.PartTwo.Sec21.FF84S4ASwap
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Holds
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43S4
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43s
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Rank

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.RankThree.PartTwo.Sec21.FF84.S4


theorem ff84Extraspecial_of_rest
    (hR : A_transvRank_stmt) : FF84Extraspecial := by
  have hsw : A_swap_stmt := A_swap_holds
  have hcen : A_cent_A5_odd_stmt := A_cent_A5_odd_holds
  have hT : A_transv_stmt := A_transv_holds
  have hPair : HypOmPair := hypOmPair_holds
  have hPar : HypOmParabolic := hypOmParabolic_holds
  have hE27 : HypOmNormalizerE27 := hypOmNormalizerE27_holds
  have hA9 : S3.A9CentralizerStmt := S3.A9_centralizer
  have hmax : A_U_max_stmt := A_U_max_holds
  have h21 : FF84_2_1 := ff84_2_1_of4 (FF79.ff79_1_3_of FF79.ff79KTypeLn_holds
      FF79.ff79KTypeLnNorm_holds FF79.ff79KGL33_holds) (FF79.H4.ff79TheoremA_simpleK4_core
          (FF79.ff79KLemmaOP_holds FF79.ff79KLemmaOExc_holds) FF79.H4.ff79AStarExists4_holds)
  have h23 : FF84_2_3 := ff84_2_3
  have h41 : FF84_4_1 := S4.ff84_4_1 h23
  have hodd : S43_odd := S4.S43_odd_of_commTheta h23 S4.s43_commThetaAll S4.S43_tstarCen₁_holds
  have h43 : FF84_4_3 := ff84_4_3_of_odd h23 hodd
  have h44 : FF84_4_4 := ff84_4_4_of_4_3 h23 h43
  have h46 : FF84_4_6 := ff84_4_6_of_4_4 h23 h43 h44
  have h47 : FF84_4_7 := S4.ff84_4_7_of h43 h44 h46 A_PiStar_holds hmax
  have hTr : S47TransportItem := s47TransportItem_of A_PiStar_holds hmax
  have hSw : S47SwapItem := s47SwapItem_of A_PiStar_holds hsw
  have h48 : FF84_4_8 := ff84_4_8_of h41 h43 h44 h46 hTr hSw
  exact ff84Extraspecial_of_items_m h21 ff84_2_2 ff84_3_5
    (S3.ff84_3_6_of_A9 hA9 ff84_3_3 ff84_3_4) h47 h48
    (ff84_4_10m_of h43 h44 h46 h47 h48 (hypS48CSb_of h41 hTr) (hypS48b2_of h41 hTr)
      (hypS49orbits_of h41 hTr A_PiStar_holds hT hcen) (hypS49S6_of h41 hTr hcen)
      hE27 hPar hPair)
    (ff84_4_11m_of h43 h44 h46 h47 h48 (hypS48CSb_of h41 hTr) (hypS48b2_of h41 hTr)
      (hypS49orbits_of h41 hTr A_PiStar_holds hT hcen) (hypS49S6_of h41 hTr hcen)
      hE27 hPar hPair (hypTransvRank_of h41 hTr A_PiStar_holds hR) hypOmNoAlt)

theorem ff84Extraspecial
    : FF84Extraspecial :=
  ff84Extraspecial_of_rest S4.A_transvRank_holds

end CFSG.RankThree.PartTwo.Sec21.FF84

end
