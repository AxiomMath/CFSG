module

public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.Hss35C2.Model.Defs
public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.Hss35C2

open CFSG.Quasithin
open CFSG.Quasithin.F53Mod (orth SecData)
open CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.Hss35C2.Model

@[expose] def f5W : orth.W :=
  ⟨Multiplicative.ofAdd (fun i : Fin 5 => if i = 4 then (0 : ZMod 2) else 1), by
  show ∑ i : Fin 5, (if i = 4 then (0 : ZMod 2) else 1) = 0
  decide⟩

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.Hss35C2
