module

public import CFSG.Quasithin.Background.Harris.Routing.LieAdapters
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.ExcThreeD4All

public section

namespace CFSG.Quasithin.G11.Harris

open CFSG.Open CFSG.Blueprint


theorem oneCompFor_fam3D4 : OneCompFor Fam3D4 :=
  oneCompFor_fam3D4_of_false fun _ _ _ _ f hf _ _ _ _ hG hX =>
    CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.false_of_trialityD4_all hf hG hX

end CFSG.Quasithin.G11.Harris
