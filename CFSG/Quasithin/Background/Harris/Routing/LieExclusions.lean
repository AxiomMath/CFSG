module

public import CFSG.Quasithin.Background.Harris.Routing.LieAdapters
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.ExcTwoF4Final

public section

namespace CFSG.Quasithin.G11.Harris

theorem oneCompFor_fam2F4 :
    OneCompFor Fam2F4 :=
  oneCompFor_fam2F4_of_false fun _ _ _ _ _ hf hf3 _ _ _ _ hG hX =>
    CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.false_of_twistedF4 hf hf3 hG hX

end CFSG.Quasithin.G11.Harris
