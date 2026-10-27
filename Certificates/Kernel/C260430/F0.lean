module

public import Certificates.Data.Kernel.B45Ind.M23

public section

namespace CFSG.KD.C260430

open CFSG.KC.B45Ind

theorem coset : coset23L = true := by
  decide +kernel

theorem flag0 : flag23L 0 = true := by
  decide +kernel

end CFSG.KD.C260430
