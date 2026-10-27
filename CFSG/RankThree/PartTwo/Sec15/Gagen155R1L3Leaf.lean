module

public import CFSG.RankThree.PartTwo.Sec15.Praeger155R1Item1730Final
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1L3Thm340
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1L3Le
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1L3L34
public import CFSG.RankThree.PartTwo.Sec15.MathAsch1513Of316

public section

namespace CFSG.RankThree.PartTwo.Sec15.GagenL3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

theorem res1ZExclLeN_su3_l3_of_316
    (h316 : Sec19.Item316)
    (h150 : Sylow155R1.Res1Thm150b Res1L3Q Res1OpenSU3Type) :
    Sylow155R1.Res1ZExclLeN Res1L3Q Res1OpenSU3Type :=
  Sylow155R1.res1ZExclLeN_su3_of_thm340_gen Ronan148M.concl142S14_holds
    Ronan149.item145BotS14_holds Ronan149.item1444S14_holds Ronan149.item149S14_holds res1QE9_l3
    (fun _ _ _ _ _ _ hR hL => item153Main_of_l3 h316 hR hL.1) (res1Thm340_l3_of_316 h316) h150

theorem res1ZExclLeN_open_l3_of_316
    (h316 : Sec19.Item316)
    (h150L2 : Sylow155R1.Res1Thm150b Res1L3Q Res1OpenL2Type)
    (h150SU3 : Sylow155R1.Res1Thm150b Res1L3Q Res1OpenSU3Type) :
    Sylow155R1.Res1ZExclLeN Res1L3Q Res1OpenType :=
  Sylow155R1.res1ZExclLeN_open_of_split (res1ZExclLeN_l2_l3_of_316_h150 h316 h150L2)
    (res1ZExclLeN_su3_l3_of_316 h316 h150SU3)

theorem step155HostE0WRes1TypeFPt_l3_of_316
    (h316 : Sec19.Item316)
    (h150L2 : Sylow155R1.Res1Thm150b Res1L3Q Res1OpenL2Type)
    (h150SU3 : Sylow155R1.Res1Thm150b Res1L3Q Res1OpenSU3Type)
    (hin : Sylow155R1.Res1L112InPt Res1L3Pt Res1OpenType) :
    Step155HostE0WRes1TypeFPt Res1L3Pt Res1OpenType :=
  step155HostE0WRes1TypeFPt_l3_of_zExcl_of_in item135_holds Ronan149.item145BotS14_holds
    Ronan149.item1444S14_holds Ronan149.item149S14_holds Ronan148M.concl142S14_holds
    (Sec14.step142LowerGenL3_of_res8 rank3II_13_1_holds
      (Sec14.ks142L3HessGenNine_of_model Sec14.ks142L3HessGenNineModel_proof)
      Sec14.step142LowerGenL3PGL_proof)
    (Res1H1.item1511R_of_item316 h316)
    (fun _ _ _ _ _ _ hR hL hnPGL hWH hY0 =>
      Res1Omega1513.omegaA_eq_of_lThreePi h316 hR hL hnPGL hWH hY0)
    (fun _ _ _ _ _ _ hR hY0 =>
      not_z3_l34_of_scriptY0 rank3II_13_1_holds (Res1Omega1513.item1513R_of_item316 h316)
        item1510R_holds step169TwoBridge_holds hR hY0)
    (fun _ _ _ _ _ _ hR hL => item153Main_of_l3 h316 hR hL)
    (res1ZExclLeN_open_l3_of_316 h316 h150L2 h150SU3) hin

theorem item1730_of_l3_316
    (h316 : Sec19.Item316) (h310 : Sec6.Item3_10)
    (h150L2 : Sylow155R1.Res1Thm150b Res1L3Q Res1OpenL2Type)
    (h150SU3 : Sylow155R1.Res1Thm150b Res1L3Q Res1OpenSU3Type)
    (hin : Sylow155R1.Res1L112InPt Res1L3Pt Res1OpenType) :
    Sec17.Item1730 :=
  item1730_of_l3Pt_316 h316 h310 (step155HostE0WRes1TypeFPt_l3_of_316 h316 h150L2 h150SU3 hin)

end CFSG.RankThree.PartTwo.Sec15.GagenL3
