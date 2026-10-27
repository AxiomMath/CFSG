module

public import CFSG.Quasithin.Background.C126Final
public import CFSG.Quasithin.Background.C126NatMain
public import CFSG.Quasithin.Background.GoldschmidtE23Final
public import CFSG.Quasithin.EmptyFaithful.A38c13FFC
public import CFSG.Quasithin.Background.B15P4Layer2Final
public import CFSG.Quasithin.Background.B5NonSQTK
public import CFSG.Quasithin.Background.E2TwoC
public import CFSG.Quasithin.Background.Sp4InfMainOne

public section

namespace CFSG.Quasithin

theorem theoremC126_of_inputs
    (hB42 : AsB42) (hDeep69 : B69.AsB69DeepInputsFour) (hE22C : E2.E22StatementC)
    (hRF : C126.RadFreeStmt)
    (hS : ∀ (G : Type) [Group G] [Finite G] (C₁ C₂ : Subgroup G → Subgroup G),
      C126.A5Stmt C₁ C₂) : TheoremC126 := by
  have hB15P4 : AsB15Part4 := B15P4.asB15Part4
  have hComp69 : B69.AsB69Component :=
    B69.asB69Component_of_deep_inputs_fourNoN hB42 asA21SQTKSection hE22C.toNoN hDeep69
  have hB69 : B69One :=
    B69.b69One_of_Sp4NoN hB42 hB15P4 asA21SQTKSection hE22C.toNoN B69.noStrongSp4
  have hE23 : E2.E23Statement := E2.e23Statement_of_nonsolvable
    (GE23.e23Nonsolvable_of_inputs hB15P4 hComp69 hB69 hE22C.toNoN)
  exact theoremC126_of_cases hE23 (fun _ _ _ _ _ => C126.Nat.natStmt_of_e23 hE23 hRF) hS

end CFSG.Quasithin
