module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Stroth78OfSmithCore
public import CFSG.RankThree.GF2n.Stroth80.SmithEightHolds
public import CFSG.RankThree.GF2n.Stroth80.Sec79MinOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec7EightSmithCore

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Certs


theorem step76EightSmithCore_holds : Step76EightSmithCoreStatement := by
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
  have hNR : Sec7NormZ0Statement := sec7NormZ0_of_inputs h56 hA
  have h73a : Stroth73aStatement :=
    stroth73a_of_cases (stroth73aNotOm4_of hNR) (stroth73aOm4_of_base zt centre om4Base)
  have hEnd : Sec7EndStatement :=
    sec7End_of_parts h34 h310chi zt centre zcard h311a h44 h45
  have hPair : Step71VanishPairStatement :=
    step71VanishPair_of_omega4 h34 h310root h310chi centre hZV zcard omegaMinusFourGeom_holds
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
  exact step76EightSmithCore_of h34 h310root h310chi h71 centre hZV zcard h52a hA hSec hV
    (sec7WVSplit_of hA hpts h52a h52b) smithOmegaPlusEight_holds

theorem stroth78Statement_holds : Stroth78Statement :=
  stroth78_of_smithCore step76EightSmithCore_holds

theorem stroth79Statement_holds : Stroth79Statement :=
  stroth79_of_inputs stroth78Statement_holds stroth51Statement_unconditional
    sec7AExistsStatement_unconditional
    (sec7ZCard_of_inputs stroth51Statement_unconditional sec7AExistsStatement_unconditional)
    (sec79MinOrder_of stroth51Statement_unconditional sec7AExistsStatement_unconditional
      (sec5NatPointsOmega_of stroth34Statement_unconditional
        (stroth310Root_of_34 stroth34Statement_unconditional)))

end Certs

end CFSG.RankThree.GF2n.Stroth80
