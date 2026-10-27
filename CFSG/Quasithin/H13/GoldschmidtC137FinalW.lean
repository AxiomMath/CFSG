module

public import CFSG.Quasithin.Background.C124HoldsE22
public import CFSG.Quasithin.H13.GoldschmidtC137U33Final
public import CFSG.Quasithin.H13.GoldschmidtC137H6Case
public import CFSG.Quasithin.H13.GoldschmidtC137L32FinalW

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.H13.U3.GC137

open CFSG.Quasithin

theorem c137StatementFiveSQTK_finalW
    (hE22 : E2.E22StatementNoN) (hC132 : ASInputs.AS_C_1_32)
    (hC134 : C134L32CorrM) : C137StatementFiveSQTK :=
  c137StatementFiveSQTK_of_cases (fun G _ _ => C124.c124StatementSQTK_of_e22 hE22 G)
    (c137CaseL32_finalW hC134) (c137CaseU33_final hC132)
    (c137CaseS6_of (fun G _ _ => C124.c124StatementSQTK_of_e22 hE22 G) hC132)

end CFSG.Quasithin.H13.U3.GC137
