module

public import CFSG.RankThree.GF2n.Stroth80.AssemblyOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec12SecondCores
public import CFSG.RankThree.GF2n.Stroth80.Sec86MinOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec7Unconditional
public import CFSG.RankThree.GF2n.Stroth80.Sec12FStarLB
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Sec12Omega6PlusQ
public import CFSG.RankThree.GF2n.Stroth80.Sec1111NotTI
public import CFSG.RankThree.GF2n.Stroth80.Sec123SL2
public import CFSG.RankThree.GF2n.Stroth80.Sec12Certified

public section

namespace CFSG.RankThree.GF2n.Stroth80

section Certs


structure StrothOpenSectionsOT : Prop where
  h65 : Stroth65Statement
  h78 : Stroth78Statement
  h79 : Stroth79Statement
  h716 : Stroth716TypeStatement
  h717 : Stroth717Statement
  h83 : Stroth83Statement
  h86 : Stroth86Statement
  h98 : Stroth98Statement
  h108 : Stroth108Statement
  h1111 : Stroth1111Statement
  ci4 : Stroth4iStatement
  nbarGe : Stroth6NbarGeStatement

theorem strothSectionsOT_of_open (S : StrothOpenSectionsOT) : StrothSectionsOT :=
  have hX : Classify.TheoremXStatement :=
    Classify.theoremX_of_inputs mcLaughlinStatement_holds
      (Classify.lemmaP_of_mcLaughlin mcLaughlinStatement_holds)
      Classify.siegelGenStatement_holds
  have h311a : Stroth311aStatement :=
    stroth311a_of_theoremX stroth34Statement_unconditional stroth310Statement_unconditional hX
      (griessCoverStatement_of_table
        CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
        griessSL34Statement_holds)
      (stroth311Conj_of_theoremX stroth34Statement_unconditional hX)
  have h51 : Stroth51Statement := stroth51Statement_unconditional
  have hA : Sec8AExistsStatement := sec8AExistsStatement_unconditional
  have hZ86 : Sec86ZCardStatement := sec86ZCard_of_51 h51 hA
  have hirr : Sec86IrredStatement := sec86Irred_of_inputs S.h83 h51 hA
    (sec86MinOrder_of h51 hA (sec5NatPointsSp_of_34 stroth34Statement_unconditional))
  have hZ7 : Sec7ZCardStatement := sec7ZCardStatement_holds
  have hgen : StrothGenByBStatement := strothGenByBStatement_certified
  { h34 := stroth34Statement_unconditional
    h37 := stroth37Statement_unconditional
    h44 := stroth44_of_312ab stroth34Statement_unconditional stroth310Statement_unconditional
      (stroth312a_of_311a stroth34Statement_unconditional h311a)
      (stroth312b_of_311a stroth34Statement_unconditional hX h311a)
      (classicalNonsolvable_of_quasisimple classicalQuasisimpleStatement_holds)
    h310 := stroth310Statement_unconditional
    h65 := S.h65
    h78 := S.h78
    h79 := S.h79
    h716 := S.h716
    h717 := S.h717
    h83 := S.h83
    h86 := S.h86
    h98 := S.h98
    h108 := S.h108
    h1111 := S.h1111
    h123 := stroth123Statement_holds
    noSp := stroth121Sp_of_order_core (stroth121SpCore_of_4i hZ86 hirr hgen S.ci4)
    noOmega := stroth121Omega_of_order_core
      (stroth121OmegaCore_of_4i hZ7 omegaSignStatement_holds hgen S.ci4)
    fstarLB := stroth12FStarLB_holds
    omega6 := stroth12Omega6_of_order_core
      (stroth12Omega6Minus_of_4i hZ7 S.h78 S.h79 omegaSignStatement_holds hgen S.ci4)
      (stroth12Omega6PlusCaseE6_of_second hZ7 S.h78 hgen S.ci4)
      (sec12Omega6PlusQStatement_of_zcard hZ7)
      (stroth12FStarIii_of_lb stroth12FStarLB_holds)
    genByB := hgen
    nt := strothNt_of_311a stroth34Statement_unconditional h311a
    nbarGe := S.nbarGe
    notTI := strothNotTI_of_1111 S.h1111 }

theorem stroth_order_step_of_open (S : StrothOpenSectionsOT) {N : ℕ} (hS : Stroth1980Below N)
    (hM : CFSG.RankThree.GF2n.Smith81.Smith1981TheoremBelow N) : Stroth1980Below (N + 1) :=
  stroth_order_step (strothSectionsOT_of_open S) hS hM

end Certs

end CFSG.RankThree.GF2n.Stroth80
