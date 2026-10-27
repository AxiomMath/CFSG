module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieAsm
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieRed

public section

namespace CFSG.Quasithin.H13.F431.Un

theorem f431UnOutLieProp_five : F431UnOutLieProp 5 2 :=
  OL5.f431UnOutLieProp_of_model5 fun _ _ h _ F₂ hinn hev hT =>
    OL5.exists_unOutRel5 h rfl F₂ hinn hev hT

end CFSG.Quasithin.H13.F431.Un
