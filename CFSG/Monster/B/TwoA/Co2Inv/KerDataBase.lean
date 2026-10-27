
module

public import CFSG.Monster.B.TwoA.Co2Inv.KerDataInputs

@[expose] public section

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert
  CFSG.Monster.B.TwoA.Census

theorem par4_lt : ∀ n, par4 n < 2 := fun n => Nat.mod_lt _ (by norm_num)

end CFSG.Monster.B.TwoA.Co2Inv
