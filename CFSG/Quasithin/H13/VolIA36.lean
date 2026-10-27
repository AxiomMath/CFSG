module

public import CFSG.Quasithin.Vol2.Ch1A3Cat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverA36

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin

theorem a36ForSQTK_holds
    : A36ForSQTK := fun Q _ hQ =>
  CFSG.QuasithinUnique.Vol2Native.a36ForSQTKCat_proved Q hQ.toCat

end CFSG.Quasithin.H13.VolI
