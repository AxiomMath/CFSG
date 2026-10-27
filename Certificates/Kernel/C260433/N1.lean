module

public import Certificates.Kernel.C260433.Chk

public section

namespace CFSG.KD.C260433

open CFSG.KC.B45Nor CFSG.Quasithin.B45Mat.Ind

theorem nor24Tr1 (z : Bool) : trChk (m24Std 1 z) (ht24 1 z) 0 = true := by
  cases z <;> decide +kernel

theorem nor24N1 : nor24K 1 = true := by decide +kernel

end CFSG.KD.C260433
