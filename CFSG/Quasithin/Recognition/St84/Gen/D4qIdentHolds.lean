module

public import CFSG.Quasithin.Recognition.St84.Gen.IdL2L2GenGlue

import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalGlue

public section

namespace CFSG.Quasithin.F112R.St84


theorem d4qIdent : D4qIdent := fun _ _ _ _ _ _ _ hF hf h1 h2 hD =>
  isAmalgamOfGroup_d4_of_d4qLocalData hf hF.1 h1 h2 hD

end CFSG.Quasithin.F112R.St84

end
