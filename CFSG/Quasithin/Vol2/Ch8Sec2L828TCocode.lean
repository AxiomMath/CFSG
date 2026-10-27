module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TCore5
public import CFSG.Quasithin.Vol2.Ch8Sec2L828SAssemble

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative commutatorElement

theorem stmt8_2_8CocodeFive_of (hE214 : ASInputs.AS_E_2_14)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal) (hcard : Mathieu.StmtH13Card)
    (hLU : HLU82) (h825 : Stmt8_2_5) (h827 : Step827)
    (hMB0 : MB0_828) (hMB2 : MB2_828) (hMB3 : MB3_828) (hSyl : Sylow822VB_828) :
    Stmt8_2_8CocodeFive := by
  intro G _ _ T L I hyp h731 h821 hc hrow H h k hH hh hC _ P U LU hP hU hLU' x hxP hxU hx5 hcLU
    hcI p hp
  subst hP hU hLU'
  have c := s828_ctx hE214 h37 h38 h39 hmod h711n hcard hLU h825 h827 hMB0 hMB3 hSyl hyp h731
    h821 hrow hH hh hC
  have := s828_core5 hMB2 hcard hrow c hxP hxU hx5 hcLU hcI p hp
  simpa only [commutatorElement_def] using this

theorem stmt8_2_8Cocode_holds (hE214 : ASInputs.AS_E_2_14)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal) (hcard : Mathieu.StmtH13Card)
    (hLU : HLU82) (h825 : Stmt8_2_5) (h827 : Step827)
    (hMB0 : MB0_828) (hMB2 : MB2_828) (hMB3 : MB3_828) (hSyl : Sylow822VB_828) :
    Stmt8_2_8Cocode :=
  stmt8_2_8Cocode_of hE214 h37 h38 h39 hmod h711n hcard hLU h825 h827 hMB0 hMB3 hSyl
    (stmt8_2_8CocodeFive_of hE214 h37 h38 h39 hmod h711n hcard hLU h825 h827 hMB0 hMB2 hMB3 hSyl)

end CFSG.Quasithin.H13
