module

public import Certificates.Data.Kernel.Misc.YamakiRepF

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.Sp62 (MULF ONE)

@[expose] noncomputable def wordF6 (g : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) ONE (fun i _ acc => MULF (g i) acc) w

end CFSG.KD.OmegaSix

end
