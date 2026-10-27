module

public import CFSG.Yardstones.Mdac756b924db.FrontierPrintBlockCExtremal
public import CFSG.RankThree.PartTwo.Sec20.SimsItem201Foote
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aItems
public import CFSG.RankThree.PartTwo.Sec15.Lempken155L3Cover

public section

namespace CFSG.Yardstones.Mdac756b924db

theorem agl81TheoremAResiduesE3_of_roots_l3
    (hGF : CFSG.RankThree.GF2n.GF2nTypeStatement)
    (hStroth : CFSG.OddStandard.HigherRank.YamadaG23.StrothSigma6)
    (h150L2 : CFSG.RankThree.PartTwo.Sec15.Sylow155R1.Res1Thm150b
      CFSG.RankThree.PartTwo.Sec15.GagenL3.Res1L3Q CFSG.RankThree.PartTwo.Sec15.Res1OpenL2Type)
    (h150SU3 : CFSG.RankThree.PartTwo.Sec15.Sylow155R1.Res1Thm150b
      CFSG.RankThree.PartTwo.Sec15.GagenL3.Res1L3Q CFSG.RankThree.PartTwo.Sec15.Res1OpenSU3Type)
    (hin : CFSG.RankThree.PartTwo.Sec15.Sylow155R1.Res1L112InPt
      CFSG.RankThree.PartTwo.Sec15.Res1L3Pt CFSG.RankThree.PartTwo.Sec15.Res1OpenType) :
    AGL81TheoremAResiduesE3 := by
  have h310 := CFSG.RankThree.GF2n.item3_10_of_gf2nTypeStatement hGF
  have h316 := CFSG.RankThree.PartTwo.Sec19.item316_of_stroth hStroth h310
  have h1730 :=
    CFSG.RankThree.PartTwo.Sec15.GagenL3.item1730_of_l3_316 h316 h310 h150L2 h150SU3 hin
  exact agl81TheoremAResiduesE3_of_blockCExtremal h1730 h316
    (CFSG.RankThree.PartTwo.Sec20.item201Contra1_of_stroth h1730 h310 hStroth)
    (CFSG.RankThree.PartTwo.Sec21.FF81.item231_of_gf2n hGF)
    (CFSG.RankThree.PartTwo.Sec21.FF81.item233_of_gf2n hGF)

theorem agl81TheoremAResiduesE3_of_roots_in
    (hGF : CFSG.RankThree.GF2n.GF2nTypeStatement)
    (hStroth : CFSG.OddStandard.HigherRank.YamadaG23.StrothSigma6)
    (hin : CFSG.RankThree.PartTwo.Sec15.Sylow155R1.Res1L112InPt
      CFSG.RankThree.PartTwo.Sec15.Res1L3Pt CFSG.RankThree.PartTwo.Sec15.Res1OpenType) :
    AGL81TheoremAResiduesE3 :=
  agl81TheoremAResiduesE3_of_roots_l3 hGF hStroth
    CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150.res1Thm150b_l3_holds
    CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150.res1Thm150b_l3_holds hin

theorem agl81TheoremAResiduesE3_of_roots_cover
    (hGF : CFSG.RankThree.GF2n.GF2nTypeStatement)
    (hStroth : CFSG.OddStandard.HigherRank.YamadaG23.StrothSigma6)
    (hcov : CFSG.RankThree.PartTwo.Sec15.Res1Omega1513.Res1CoverL3) :
    AGL81TheoremAResiduesE3 :=
  agl81TheoremAResiduesE3_of_roots_in hGF hStroth
    (CFSG.RankThree.PartTwo.Sec15.res1L112InPt_l3Pt_of_316_of_cover
      (CFSG.RankThree.PartTwo.Sec19.item316_of_stroth hStroth
        (CFSG.RankThree.GF2n.item3_10_of_gf2nTypeStatement hGF)) hcov)

theorem agl81TheoremAResiduesE3_of_roots_two
    (hGF : CFSG.RankThree.GF2n.GF2nTypeStatement)
    (hStroth : CFSG.OddStandard.HigherRank.YamadaG23.StrothSigma6) :
    AGL81TheoremAResiduesE3 :=
  agl81TheoremAResiduesE3_of_roots_cover hGF hStroth
    (CFSG.RankThree.PartTwo.Sec15.Res1Cover.res1CoverL3_of_item316
      (CFSG.RankThree.PartTwo.Sec19.item316_of_stroth hStroth
        (CFSG.RankThree.GF2n.item3_10_of_gf2nTypeStatement hGF)))

end CFSG.Yardstones.Mdac756b924db
