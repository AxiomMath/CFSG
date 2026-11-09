module

public import Certificates.Data.Kernel.B45Ind.M23
public import Certificates.Data.Kernel.B45Ind.FlagK

public section

namespace CFSG.KD.C260430

open CFSG.KC.B45Ind

theorem flag2 : flag23L 2 = true := by
  rw [flag23L_eq_K]
  decide +kernel

end CFSG.KD.C260430
