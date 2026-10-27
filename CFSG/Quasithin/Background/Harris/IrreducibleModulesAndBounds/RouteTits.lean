module

public import CFSG.Quasithin.Background.Harris.Routing.LieAdapters
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.ExcTits

public section

namespace CFSG.Quasithin.G11.Harris

open CFSG.Open CFSG.Blueprint


theorem oneCompFor_famTits_of_smith : OneCompFor FamTits :=
  oneCompFor_famTits_of_false fun _ _ _ _ _ _ _ _ hG hX =>
    CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.false_of_tits hG hX

end CFSG.Quasithin.G11.Harris
