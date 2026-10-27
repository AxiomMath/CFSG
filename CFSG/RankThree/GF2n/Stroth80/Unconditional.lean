module

public import CFSG.RankThree.GF2n.Stroth80.OpenSections
public import CFSG.RankThree.GF2n.Stroth80.Sec4Assembly
public import CFSG.RankThree.GF2n.Stroth80.GriessProof
public import CFSG.RankThree.GF2n.Stroth80.GriessSL34Proof
public import CFSG.RankThree.GF2n.Stroth80.Sec311Assembly
public import CFSG.RankThree.GF2n.Stroth80.Sec311ConjX
public import CFSG.RankThree.GF2n.Stroth80.Sec312a
public import CFSG.RankThree.GF2n.Stroth80.Sec312b

public section

namespace CFSG.RankThree.GF2n.Stroth80

section Certs

theorem theoremXStatement_holds : Classify.TheoremXStatement :=
  Classify.theoremX_of_inputs mcLaughlinStatement_holds
    (Classify.lemmaP_of_mcLaughlin mcLaughlinStatement_holds) Classify.siegelGenStatement_holds

theorem stroth311aStatement_unconditional : Stroth311aStatement :=
  stroth311a_of_theoremX stroth34Statement_unconditional stroth310Statement_unconditional
    theoremXStatement_holds
    (griessCoverStatement_of_table
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
      griessSL34Statement_holds)
    (stroth311Conj_of_theoremX stroth34Statement_unconditional theoremXStatement_holds)

theorem strothNtStatement_unconditional : StrothNtStatement :=
  strothNt_of_311a stroth34Statement_unconditional stroth311aStatement_unconditional

theorem stroth312aStatement_unconditional : Stroth312aStatement :=
  stroth312a_of_311a stroth34Statement_unconditional stroth311aStatement_unconditional

theorem stroth312bStatement_unconditional : Stroth312bStatement :=
  stroth312b_of_311a stroth34Statement_unconditional theoremXStatement_holds
    stroth311aStatement_unconditional

theorem stroth44Statement_unconditional : Stroth44Statement :=
  stroth44_of_312ab stroth34Statement_unconditional stroth310Statement_unconditional
    stroth312aStatement_unconditional stroth312bStatement_unconditional
    (classicalNonsolvable_of_quasisimple classicalQuasisimpleStatement_holds)

theorem stroth45Statement_unconditional : Stroth45Statement :=
  stroth45_of_44 stroth34Statement_unconditional stroth310Statement_unconditional
    stroth44Statement_unconditional

end Certs

end CFSG.RankThree.GF2n.Stroth80
