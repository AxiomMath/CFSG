module

public import CFSG.Quasithin.Recognition.St84.Gen.St84LLSplit

import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIdent
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndec
import CFSG.Quasithin.Recognition.St84.Gen.D4qIdentHolds

public section

namespace CFSG.Quasithin.F112R.St84


theorem g2qIdent : G2qIdent := fun _ _ _ _ _ _ _ hF hf h1 h2 hD =>
  hD.isAmalgamOfGroup_g2_of_indec hf hF.1 h1 h2 (hD.commutator_pCoreOf_right hf hF.1 h1 h2)

theorem idL2L2GenW_of_odd (hodd : St84LLOdd) : IdL2L2GenW :=
  idL2L2GenW_of_parts (st84LLLocal_of_odd hodd) g2qIdent d4qIdent

end CFSG.Quasithin.F112R.St84

end
