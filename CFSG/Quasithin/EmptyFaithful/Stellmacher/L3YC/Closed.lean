module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Final
public import CFSG.Quasithin.Background.C1PackSolvFinal
public import CFSG.Quasithin.Background.A3FactsSchreierFinal
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationFinal
public import CFSG.Quasithin.Background.C2PushH129
public import CFSG.Quasithin.Background.C129NativeMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Final
public import CFSG.Quasithin.Background.B15P4Layer2Final
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Holds
public import CFSG.Quasithin.H13.VolIA36

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace Stellmacher.L3YC

theorem l3YCCommNotCentral_holds :
    SzC4.L3YCCommNotCentral := by
  have hS : A3Facts.SchreierSQTK := A3Facts.schreierSQTK
  have hA3 := A3Facts.a3_inputs_of_a134_schreier A3Facts.a134ForSQTK hS
  exact l3YCCommNotCentral_of
    (A3Facts.stageLemma14111_of_schreier_solv gNCampbellC128Solv hS A10.theorem1391)
    (stageLemma14113_of_stages_h129_used (stageLemma14110_of_theorem1391 A10.theorem1391)
      (asc129StatementUsed_of_native (Bridge.asB113_of_timmesfeld B15P4.asB15Part4)))
    H13.VolI.a36ForSQTK_holds hA3.1 hA3.2.1 hA3.2.2
    (A38c14.a312ForSQTK_of_residual A3Facts.a134ForSQTK hS
      A38c17.a312ResidualRest2_holds.toRest3.toRest4.toRest10.toRest)

end Stellmacher.L3YC

end CFSG.Quasithin
