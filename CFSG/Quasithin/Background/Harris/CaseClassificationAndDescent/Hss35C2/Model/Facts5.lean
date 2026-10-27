module

public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.Hss35C2.Model.Defs

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.Hss35C2.Model

open CFSG.Quasithin CFSG.Quasithin.F53Mod Equiv

instance instDecidableMemZax (z : Vec) : Decidable (z ∈ Zax) :=
  decidable_of_iff _ mem_Zax.symm

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.Hss35C2.Model
