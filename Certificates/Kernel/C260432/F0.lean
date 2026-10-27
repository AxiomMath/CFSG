module

public import Certificates.Data.Kernel.B45Ind.M24

public section

namespace CFSG.KD.C260432

open CFSG.KC.B45Ind

theorem coset : coset24L = true := by
  decide +kernel

theorem flag0 : flag24L 0 = true := by
  decide +kernel

end CFSG.KD.C260432
