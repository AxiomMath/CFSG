module

public import CFSG.Quasithin.Background.C126Holds
public import CFSG.Quasithin.Background.C126RFFinal
public import CFSG.Quasithin.Background.C126A5Main
public import CFSG.Quasithin.Background.KnownMultTypes

public section

namespace CFSG.Quasithin

theorem theoremC126_holds

    (hB42 : AsB42) (hDeep69 : B69.AsB69DeepInputsFour) (hE22C : E2.E22StatementC) :
    TheoremC126 :=
  theoremC126_of_inputs hB42 hDeep69 hE22C (C126.radFreeStmt_of_e22 hE22C.toNoN mult2Fact)
    fun _ _ _ _ _ => C126.a5Stmt_of_radFree (C126.radFreeStmt_of_e22 hE22C.toNoN mult2Fact)

end CFSG.Quasithin
