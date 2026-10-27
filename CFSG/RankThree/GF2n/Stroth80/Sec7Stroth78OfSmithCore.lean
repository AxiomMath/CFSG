module

public import CFSG.RankThree.GF2n.Stroth80.Sec52bProof
public import CFSG.RankThree.GF2n.Stroth80.Sec7VanishGeomOm4
public import CFSG.RankThree.GF2n.Stroth80.Sec78CRW
public import CFSG.RankThree.GF2n.Stroth80.Sec78ConjOm4
public import CFSG.RankThree.GF2n.Stroth80.Sec78Zt
public import CFSG.RankThree.GF2n.Stroth80.Sec7CardAlpha
public import CFSG.RankThree.GF2n.Stroth80.Sec7CommN
public import CFSG.RankThree.GF2n.Stroth80.Sec7EightTamePoint
public import CFSG.RankThree.GF2n.Stroth80.Sec7EightTameSmith
public import CFSG.RankThree.GF2n.Stroth80.Sec7EightWildMeet
public import CFSG.RankThree.GF2n.Stroth80.Sec7Index72
public import CFSG.RankThree.GF2n.Stroth80.Sec7NOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec7Om10
public import CFSG.RankThree.GF2n.Stroth80.Sec7Step77Moves
public import CFSG.RankThree.GF2n.Stroth80.Sec7Step77TameComm
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsSchur
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsVanish
public import CFSG.RankThree.GF2n.Stroth80.Sec7SylowLB
public import CFSG.RankThree.GF2n.Stroth80.Sec7WVGe
public import CFSG.RankThree.GF2n.Stroth80.Sec7WVNe6Om4
public import CFSG.RankThree.GF2n.Stroth80.Step76NoWildSix
public import CFSG.RankThree.GF2n.Stroth80.Step78Ineq

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Certs

theorem stroth78_of_smithCore (hSC : Step76EightSmithCoreStatement) : Stroth78Statement := by
  have h34 : Stroth34Statement := stroth34Statement_unconditional
  have h310 : Stroth310Statement := stroth310Statement_unconditional
  have h311a : Stroth311aStatement := stroth311aStatement_unconditional
  have h44 : Stroth44Statement := stroth44Statement_unconditional
  have h45 : Stroth45Statement := stroth45Statement_unconditional
  have h51 : Stroth51Statement := stroth51Statement_unconditional
  have hA : Sec7AExistsStatement := sec7AExistsStatement_unconditional
  have hA8 : Sec8AExistsStatement := sec8AExistsStatement_unconditional
  have h52a : Stroth52aStatement := stroth52aStatement_holds
  have h52b : Stroth52bStatement := stroth52bStatement_holds
  have om4Geom : OmegaMinusFourGeomStatement := omegaMinusFourGeom_holds
  have h310chi : Stroth310ChiStatement := stroth310Chi_of_34 h34
  have h310root : Stroth310RootStatement := stroth310Root_of_34 h34
  have h56 : Stroth56NatStatement := stroth56Nat_of_34 h34
  have hpts : Sec5NatPointsOmegaStatement := sec5NatPointsOmega_of h34 h310root
  have hptsSp : Sec5NatPointsSpStatement := sec5NatPointsSp_of h34 h310root
  have h52c : Stroth52cStatement := stroth_5_2c_of_chi h310chi
  have centre : Sec7CentreMpStatement := sec7CentreMp_of_inputs h51 h52a hA
  have zt : Sec7ZtStatement :=
    sec7Zt_of_inputs h34 h310 h51 h52a hA hA8 h56 hpts hptsSp
  have cv : Sec7CVStatement := sec7CV_of_inputs h34 h310root hA h52b
  have conjOm4 : Sec7ConjOm4Statement := sec7ConjOm4_of_inputs h34 hA hpts zt
  have zcard : Sec7ZCardStatement := sec7ZCard_of_inputs h51 hA
  have hZV : Sec7ZVStatement := sec7ZV_of_parts zt centre h310chi
  have om4Base : Stroth73aOm4BaseStatement :=
    stroth73aOm4Base_of_psi h34 h310chi centre hZV zcard
      (stroth73aOm4PsiCore_of h34 h310root)
  have hSch : Sec7SchurStatement := sec7Schur_of_parts h34 h310chi centre hZV zcard
  have hK : Sec7CRWStatement := sec7CRW_of_inputs h34 h310chi h51 h52a hA hSch
  have nOrder : Sec7NOrderStatement := sec7NOrder_of h34 h51 hA hpts
  have wvOrder : Sec7WVOrderStatement :=
    sec7WVOrder_of nOrder h52a h52b h52c hA hpts
  have wvGe : Sec7WVGeStatement := sec7WVGe_of h34 wvOrder hA hpts h52a h52b h52c
  have wvGeOm4 : Sec7WVGeOm4Statement :=
    sec7WVGeOm4_of wvOrder (sec7WVNe6Om4_of h34 hA hpts h52a h52b h52c)
  have step78Ineq : Step78IneqStatement := step78Ineq_of hA hpts h52a h52b h52c hZV
  have hNR : Sec7NormZ0Statement := sec7NormZ0_of_inputs h56 hA
  have hNC : Sec7ConjStatement := sec7Conj_of_parts h56 centre zt
  have h73a : Stroth73aStatement :=
    stroth73a_of_cases (stroth73aNotOm4_of hNR) (stroth73aOm4_of_base zt centre om4Base)
  have hcard : Sec73CardStatement :=
    sec73Card_of_parts (sec73CardAlpha_of_inputs h34 h310root h52a hA h310chi)
      (sec73CardBeta_of_inputs hA hpts h52a h52b h310chi) wvGeOm4
  have h73cOm4 : Stroth73cOm4Statement := stroth73cOm4_of h73a cv hcard conjOm4
  have h72 : Stroth72Statement :=
    stroth72_of_index (sec7CommN_of_34 h34 h310 h311a) zcard
      (step72Index_of_inputs h34 h310root h52a h52b hA hpts hZV cv hNC conjOm4 om4Base
        hNR)
  have h73b : Stroth73bStatement := stroth73b_of_72 h72 h73a hZV zt centre hNC conjOm4
  have hTr : Stroth73bTransStatement := stroth73bTrans_of h73b hNC conjOm4
  have sylowLB : Sec7SylowLBStatement := sec7SylowLB_of_34 h34
  have hEnd : Sec7EndStatement :=
    sec7End_of_parts h34 h310chi zt centre zcard h311a h44 h45
  have hPair : Step71VanishPairStatement :=
    step71VanishPair_of_omega4 h34 h310root h310chi centre hZV zcard om4Geom
      omegaMinusFourSingularTrans_holds
  have hV : Step71VanishStatement :=
    step71Vanish_of_steps (step71VanishBound_of_pair hPair h52b h310chi) wvOrder
      wvGeOm4 wvGe
      (step71VanishOmega10_of h34 h310root h52a h52b hPair centre hZV zcard)
  have hT : Step71TypeStatement :=
    step71Type_of_steps hV (step71TypeSec_of_inputs h52a h52b hA h310chi hpts)
      (sec7WVSecOrder_of_points hpts)
  have q7 : Sec7Q7Statement :=
    sec7Q7_of_kernel hA h34 h310root h52a h52b cv
      (sec7Q7Kernel_of_inputs h34 h310root)
  have h71 : Stroth71Statement :=
    stroth71_of_steps hV hT
      (step71close_of_parts (close71TI_of h73a hZV)
        (close71Sylow_of_parts h34 h310chi h311a hZV h73a q7)
        (close71E_of_parts h34 h310chi centre hZV hK hSch h52a hA hV)
        (close71Final_of_end hEnd))
  have hSec : Sec7WVSecCardStatement := sec7WVSecCard_of hA hpts h52a h52b
  have step77One : Step77OneStatement := step77One_of_notNorm
    (step77OneNotNorm_of_inputs h34 h310root h71 h310chi centre hZV zcard h52a hA hSec
      hK h73a h73cOm4 cv sec7VtIrred_holds) om4Base
  have step77FromOne : Step77FromOneStatement := step77FromOne_of_core
    (step77FromOneCore_of_stmts h34 h310root h71 h310chi centre hZV zcard h52a h52b
      hA hpts)
  have noWildSix : Step76NoWildSixCoreStatement :=
    step76NoWildSixCore_of h34 hA hpts h52a h52b h310chi hV
  have eightTW : Step76EightKTameWildStatement := step76EightKTameWild_of
    (step76EightTameConj_of_point (step76EightTamePoint_of h34 h310root hZV) h56)
      (step76EightKTame_of_smith_core h34 h310root h310chi h71 centre hZV zcard h52a hA
        hSec hV hSC)
  have eightWW : Step76EightKWildWildStatement :=
    step76EightKWildWild_of_witness h52a hA h310chi hSec h71 hZV
      (step76EightWildWitness_of_moves_meet h34 h310chi h71 centre hZV zcard h52a hA
        hSec
        (step76EightWildMoves_of_inputs h34 h71 h310chi centre hZV zcard h52a hA hpts
          (sec7WVSplit_of hA hpts h52a h52b))
        (step76EightWildMeet_of_inputs h34 h71 h310chi centre hZV zcard h52a hA))
      eightTW
  have step76E : Step76EStatement :=
    step76E_of_cases h71 (step76NoWildSix_of h71 noWildSix)
      (step76Eight_of_K (step76EightK_of_parts eightTW eightWW)
        h34 h310chi centre hZV zcard hK hSch h52a hA hV)
  have h76 : Stroth76Statement := stroth76_of_steps hNR centre hZV hTr sylowLB step76E hEnd
  have h73c : Stroth73cStatement := stroth73c_of_cases (stroth73cNotOm4_of h73a hNC cv) h73cOm4
  have h77 : Stroth77Statement :=
    stroth77_of_steps h76 h71 h73c centre step77One
      (step77Two_of_one step77One step77FromOne) (step77End_of_one step77One step77FromOne)
  have h78 : Stroth78Statement := stroth78_of_inputs h77 nOrder wvOrder step78Ineq wvGe

  exact h78

end Certs

end CFSG.RankThree.GF2n.Stroth80
