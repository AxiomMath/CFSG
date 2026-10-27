module

public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrAssembly
public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerSplit
public import CFSG.RankThree.GF2n.Stroth80.Sec7WVMinOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec79MinOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec715ConjKappa
public import CFSG.RankThree.GF2n.Stroth80.Sec715CentProof
public import CFSG.RankThree.GF2n.Stroth80.Sec713Y

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

theorem sec715Irr_of_leaves (hExt : Ext1VanishingD4Statement)
    (hRoot8 : Omega8LongRootRankStatement) (h710 : Stroth710Statement)
    (hConfig : Sec715LayerConfigStatement) (hIrrA : Sec715IrrConfigAStatement) :
    Sec715IrrStatement := by
  have h34 := stroth34Statement_unconditional
  have h310chi := stroth310Chi_of_34 h34
  have hA := sec7AExistsStatement_unconditional
  have hCent : Sec715CentStatement :=
    sec715Cent_of_parts h34 h310chi stroth51Statement_unconditional stroth52aStatement_holds hA
      sec7ZCardStatement_holds sec7VtIrredStatement_holds sec7CVStatement_holds
      sec7SchurStatement_holds
  exact sec715Irr_of_configs h34 stroth310RootStatement_unconditional h310chi
    stroth51Statement_unconditional stroth52aStatement_holds stroth52bStatement_holds
    sec7NOrderStatement_holds hA sec7ZtStatement_holds sec7ZCardStatement_holds
    sec7CentreMpStatement_holds sec7ZVStatement_holds
    (sec7CommN_of_311b stroth311bCommStatement_unconditional) sec7CRWStatement_holds
    (sec713Y_of_inputs h34 stroth311aStatement_unconditional stroth51Statement_unconditional hA
      sec5NatPointsOmegaStatement_unconditional)
    hCent (sec715Conj_of_layerSplit (sec715LayerSplit_of stroth34Statement_unconditional
        stroth310RootStatement_unconditional (stroth310Chi_of_34 stroth34Statement_unconditional)
        stroth51Statement_unconditional stroth52aStatement_holds stroth52bStatement_holds
        sec7NOrderStatement_holds sec7ZCardStatement_holds sec7CRWStatement_holds
        sec7CentreMpStatement_holds sec7CVStatement_holds sec7AExistsStatement_unconditional hExt
        hRoot8
        (sec7WVMinOrder_of sec7AExistsStatement_unconditional
            sec5NatPointsOmegaStatement_unconditional stroth52aStatement_holds
            stroth52bStatement_holds)
        (sec79MinOrder_of stroth51Statement_unconditional sec7AExistsStatement_unconditional
            sec5NatPointsOmegaStatement_unconditional)) hCent h710) hConfig
    hIrrA

end CFSG.RankThree.GF2n.Stroth80.S715L
