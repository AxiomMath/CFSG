module

public import CFSG.Quasithin.MS93.S52iMain
public import CFSG.Quasithin.MS93.FFMain
public import CFSG.Quasithin.H13.A5S1521b

public section

namespace CFSG.Quasithin.MS93

theorem S5.s52i_holds :
    S5.S52i :=
  S52i.s52i_of ms14AS_holds fun _ _ _ _ _ _ hS f hf hQ =>
    H13.A5.sqtkGroup_of_surjective_quasisimple hS f hf hQ

end CFSG.Quasithin.MS93
