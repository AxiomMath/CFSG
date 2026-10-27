module

public import CFSG.Quasithin.Vol2.Ch3g316
public import CFSG.Quasithin.Vol2.Ch3xB513
public import CFSG.Quasithin.Vol2.Ch3nE2
public import CFSG.Quasithin.EmptyFaithful.A38c13FFC
public import CFSG.Quasithin.Background.GoldschmidtB69DeepFour
public import CFSG.Quasithin.Background.GoldschmidtE23Final
public import CFSG.Quasithin.Background.SmithB42Holds
public import CFSG.Quasithin.Background.B5NonSQTK
public import CFSG.Quasithin.Background.B15P4Layer2Final

public section

namespace CFSG.Quasithin.Ch3T316W

theorem theorem316Statement_of
    (hB513N : B513Nonsolvable) (hE213 : Ch3n.E213Member) (hE215 : Ch3n.E215Member)
    (h22N : E2.E22StatementNoN) (hC58 : TheoremC58) : Theorem316Statement := by
  have hB69 : B69One :=
    B69.b69One_of_Sp4NoN asB42_holds B15P4.asB15Part4 asA21SQTKSection h22N B69.noStrongSp4
  have hComp : B69.AsB69Component :=
    B69.asB69Component_of_deep_inputs_fourNoN asB42_holds asA21SQTKSection h22N
      (B69.asB69DeepInputsFour_holds h22N)
  have hE23 : E2.E23Nonsolvable :=
    GE23.e23Nonsolvable_of_inputs B15P4.asB15Part4 hComp hB69 h22N
  exact theorem316Statement_of_core_inputs hC58
    (d15AsPrintedSQTK_of_nonsolvable (d125NonsolvableSQTK_of_b69One hB69))
    (b513_of_nonsolvable hB513N)
    (e213Three_of_nonsolvable (Ch3n.e213ThreeNonsolvable_of_member hE213))
    (e215_of_nonsolvable (Ch3n.e215Nonsolvable_of_member hE215))
    (as316SylowNonsolvable_of_inputs (Ch3g316.gen316_proved hB69 hE23))

end CFSG.Quasithin.Ch3T316W
