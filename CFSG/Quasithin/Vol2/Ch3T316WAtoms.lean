module

public import CFSG.Quasithin.Vol2.Ch3xC58NSFinal
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
public import CFSG.Quasithin.Background.C126Final
public import CFSG.Quasithin.Background.C126NatMain
public import CFSG.Quasithin.Background.C126A5Main
public import CFSG.Quasithin.Background.C126RFFinal
public import CFSG.Quasithin.Background.GoldschmidtE23Final
public import CFSG.Quasithin.EmptyFaithful.A38c13FFC
public import CFSG.Quasithin.Background.GoldschmidtB69DeepFour
public import CFSG.Quasithin.Vol2.Ch3xC58NSMPB
public import CFSG.Quasithin.Vol2.Ch3xC58NSEmb

public section

namespace CFSG.Quasithin.Ch3T316W

theorem theoremC58_of_atoms
    (h22N : E2.E22StatementNoN) : TheoremC58 := by
  have hB69 : B69One :=
    B69.b69One_of_Sp4NoN asB42_holds B15P4.asB15Part4 asA21SQTKSection h22N B69.noStrongSp4
  have hComp : B69.AsB69Component :=
    B69.asB69Component_of_deep_inputs_fourNoN asB42_holds asA21SQTKSection h22N
      (B69.asB69DeepInputsFour_holds h22N)
  have hE23 : E2.E23Nonsolvable :=
    GE23.e23Nonsolvable_of_inputs B15P4.asB15Part4 hComp hB69 h22N
  have hE23S : E2.E23Statement := E2.e23Statement_of_nonsolvable hE23
  have hRF : C126.RadFreeStmt := C126.radFreeStmt_of_e22 h22N mult2Fact
  have h126 : TheoremC126 :=
    theoremC126_of_cases hE23S (fun _ _ _ _ _ => C126.Nat.natStmt_of_e23 hE23S hRF)
      (fun _ _ _ _ _ => C126.a5Stmt_of_radFree hRF)
  exact theoremC58_of_solvable_nonsolvable
    (EmptyFaithfulMultiple.input311Solvable_of
      (G64.inputC512G64_of_lemmaG64 (G64.lemmaG64_of_b5 asB56_holds)))
    (C58NS.theorem311Nonsolvable_of h126 C58NS.minParabolicBlockSubnormal_holds
      C58NS.embedLocal_holds)

end CFSG.Quasithin.Ch3T316W
