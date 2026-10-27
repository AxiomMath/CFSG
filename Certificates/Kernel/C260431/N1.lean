module

public import Certificates.Kernel.C260431.Chk

public section

namespace CFSG.KD.C260431

open CFSG.KC.B45Nor CFSG.Quasithin.B45Mat.Ind

theorem nor23Tr1 (z : Bool) : trChk (m23Std 1 z) (ht23 1 z) 0 = true := by
  cases z <;> decide +kernel

theorem nor23N1 : nor23K 1 = true := by decide +kernel

end CFSG.KD.C260431
