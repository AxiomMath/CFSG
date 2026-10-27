module

public import Certificates.Kernel.C260402.Pins

public section

namespace CFSG.KD.C260402

theorem len34 : T34A.length = 34 ∧ T34B.length = 34 ∧ T34G11.length = 34 := by
  decide +kernel

theorem lenP70a : P70aC.length = 340 := by
  decide +kernel

end CFSG.KD.C260402

end
