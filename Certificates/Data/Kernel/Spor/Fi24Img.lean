module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Spor.Mat3Sound

#kc_repo #kc_ktree CFSG.KD.Fi24Img MT "Certificates/Kernel/Sporadic/Fi24Br/data/mats.bin" 152491 5 3964766 4025252237917697900

public section

namespace CFSG.KD.Fi24Img

@[expose] noncomputable def img (k : Nat) : Matrix (Fin 781) (Fin 781) (ZMod 3) :=
  CFSG.KS.Mat3.mat3 781 609961 (MT k)

end CFSG.KD.Fi24Img

end
