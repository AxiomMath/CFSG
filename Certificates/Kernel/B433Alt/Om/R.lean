module

public import Certificates.Kernel.B433Alt.OmOK
public import Certificates.Data.Kernel.B433Alt.OmPl
import CFSG.Certificates.Kernel.BabyMonster.LoadRange
public import Mathlib

set_option maxRecDepth 100000

public section

namespace CFSG.KD.B4AN

@[expose] noncomputable def relPlChk (k : Nat) : Bool :=
  CFSG.KC.B4A.relPlOK MS (omRels.getD (k / 19) []) (k % 19)

end CFSG.KD.B4AN

#bm_range CFSG.KD.B4AN rel 0 1083 relPlChk

end
