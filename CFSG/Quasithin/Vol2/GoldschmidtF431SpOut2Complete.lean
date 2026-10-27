module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOut2FourG

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.Blueprint

theorem f431Out_psp (f : ℕ) (hf : IsSec53Param .PSp 2 f) : F431Out .PSp 2 f :=
  (f431_sp_inputs_of_lie (fun f _ => f431SpLieProp f) (fun _ _ hf3 => f431SpOutLieProp hf3)
    f431Out_four_of_lie).2 f hf

theorem f431SpLocal_psp (f : ℕ) : F431SpLocal f :=
  f431SpLocal_of_lie (f431SpLieProp f)

end CFSG.Quasithin.H13.F431
