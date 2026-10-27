module

public import Certificates.Kernel.C260433.Chk

public section

namespace CFSG.KD.C260433

open CFSG.KC.B45Nor CFSG.Quasithin.B45Mat.Ind

theorem nor24Tr2 (z : Bool) : trChk (m24Std 2 z) (ht24 2 z) 0 = true := by
  cases z <;> decide +kernel

theorem nor24N2 : nor24K 2 = true := by decide +kernel

end CFSG.KD.C260433
