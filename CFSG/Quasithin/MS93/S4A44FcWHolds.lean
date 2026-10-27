module

public import CFSG.Quasithin.MS93.S4A44FcW
public import CFSG.Quasithin.MS93.FFMain
public import CFSG.Quasithin.H13.A5S1521b

public section

namespace CFSG.Quasithin.MS93.S4A

theorem s4CFFcW_holds
    (h32 : S32) : S4CFFcW :=
  s4CFFcW_of ms14AS_holds (fun _ _ _ _ _ _ hS f hf hQ =>
    H13.A5.sqtkGroup_of_surjective_quasisimple hS f hf hQ) h32

end CFSG.Quasithin.MS93.S4A
