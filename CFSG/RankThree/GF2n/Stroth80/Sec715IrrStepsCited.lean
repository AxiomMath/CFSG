module

public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrCited
public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerConfigProof
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrAOf

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

theorem sec715Irr_of_steps (hExt : Ext1VanishingD4Statement)
    (hRoot8 : Omega8LongRootRankStatement) (hTri : Omega8TrialityStatement)
    (hEnd : Omega8EndScalarStatement) (h710 : Stroth710Statement)
    (hNonOrth : Sec715NonOrthNbrsStatement) (hLine : Sec715HasLineStatement)
    (hSame : Sec715SameLineOrthStatement) (hRootE : Sec715RootEltStatement) :
    Sec715IrrStatement := by
  have h34 := stroth34Statement_unconditional
  have h310chi := stroth310Chi_of_34 h34
  exact sec715Irr_of_leaves hExt hRoot8 h710
    (sec715LayerConfig_of (sec715LayerSplit_of stroth34Statement_unconditional
        stroth310RootStatement_unconditional (stroth310Chi_of_34 stroth34Statement_unconditional)
        stroth51Statement_unconditional stroth52aStatement_holds stroth52bStatement_holds
        sec7NOrderStatement_holds sec7ZCardStatement_holds sec7CRWStatement_holds
        sec7CentreMpStatement_holds sec7CVStatement_holds sec7AExistsStatement_unconditional hExt
        hRoot8
        (sec7WVMinOrder_of sec7AExistsStatement_unconditional
            sec5NatPointsOmegaStatement_unconditional stroth52aStatement_holds
            stroth52bStatement_holds)
        (sec79MinOrder_of stroth51Statement_unconditional sec7AExistsStatement_unconditional
            sec5NatPointsOmegaStatement_unconditional)) hTri hEnd h34
      stroth310RootStatement_unconditional h310chi stroth51Statement_unconditional
      stroth52aStatement_holds stroth52bStatement_holds sec7NOrderStatement_holds
      sec7ZCardStatement_holds sec7CRWStatement_holds sec7CentreMpStatement_holds
      (sec7CommN_of_311b stroth311bCommStatement_unconditional) sec7CVStatement_holds
      sec7AExistsStatement_unconditional)
    (sec715IrrA_of h310chi stroth52aStatement_holds sec7CRWStatement_holds
      sec7CentreMpStatement_holds hNonOrth hLine hSame hRootE)

end CFSG.RankThree.GF2n.Stroth80.S715L
