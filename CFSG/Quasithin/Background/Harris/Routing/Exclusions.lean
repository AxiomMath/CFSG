module

public import CFSG.Quasithin.Background.Harris.Routing.Adapters
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.ExclusionSuzuki
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.ExclusionUnitary
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.SporadicHeJ4
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.SporadicJ2HSRu
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.SporadicM11J1
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.SporadicM23

public section

namespace CFSG.Quasithin.G11.Harris

theorem oneCompFor_famSpor_M23 :
    OneCompFor (FamSpor .M23) :=
  oneCompFor_famSpor_of_false .M23 fun _ _ _ _ _ _ _ _ hG hM => CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.false_of_M23 hG hM

theorem oneCompFor_famSpor_M11 :
    OneCompFor (FamSpor .M11) :=
  oneCompFor_famSpor_of_false .M11 fun _ _ _ _ _ _ _ _ hG hM => CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.false_of_M11 hG hM

theorem oneCompFor_famSpor_J1 :
    OneCompFor (FamSpor .J1) :=
  oneCompFor_famSpor_of_false .J1 fun _ _ _ _ _ _ _ _ hG hM => CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.false_of_J1 hG hM

theorem oneCompFor_famSpor_He :
    OneCompFor (FamSpor .He) :=
  oneCompFor_famSpor_of_false .He fun _ _ _ _ _ _ _ _ hG hM => CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.false_of_He hG hM

theorem oneCompFor_famSpor_J4 :
    OneCompFor (FamSpor .J4) :=
  oneCompFor_famSpor_of_false .J4 fun _ _ _ _ _ _ _ _ hG hM => CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.false_of_J4 hG hM

theorem oneCompFor_famSpor_J2 :
    OneCompFor (FamSpor .J2) :=
  oneCompFor_famSpor_of_false .J2 fun _ _ _ _ _ _ _ _ hG hM => CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.false_of_J2 hG hM

theorem oneCompFor_famSpor_HS :
    OneCompFor (FamSpor .HS) :=
  oneCompFor_famSpor_of_false .HS fun _ _ _ _ _ _ _ _ hG hM => CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.false_of_HS hG hM

theorem oneCompFor_famSpor_Ru :
    OneCompFor (FamSpor .Ru) :=
  oneCompFor_famSpor_of_false .Ru fun _ _ _ _ _ _ _ _ hG hM => CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.false_of_Ru hG hM

theorem oneCompFor_famSz :
    OneCompFor FamSz :=
  oneCompFor_famSz_of_false fun _ _ _ _ _ hf hf3 _ _ _ _ hG hS => CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.false_of_Suzuki hf hf3 hG hS

theorem oneCompFor_famU3 :
    OneCompFor FamU3 :=
  oneCompFor_famU3_of_false fun _ _ _ _ _ hf _ _ _ _ hG hU => CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.false_of_unitaryEven hf hG hU

end CFSG.Quasithin.G11.Harris
