module

public import CFSG.Quasithin.H13.GoldschmidtC137SQFinal
public import CFSG.Quasithin.H13.GoldschmidtC137ZfFinalW

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.H13.U3.GC137

open CFSG.Quasithin

section Complete

theorem c137StatementFiveZ_completeW
    (hE22 : E2.E22StatementNoN) (hC132 : ASInputs.AS_C_1_32)
    (hC134 : C134L32CorrM) : C137StatementFiveZ :=
  c137StatementFiveZ_finalW hE22 hC132 hC134 c137SQTKSupply_holds

end Complete

end CFSG.Quasithin.H13.U3.GC137
