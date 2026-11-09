module

public import Certificates.Kernel.B45.C260393D

set_option maxRecDepth 400000

public section

namespace CFSG.KD.B45.C260393

theorem W.c3 : ckW (nat_lit 3) = true := by
  rw [ckW_eq]
  decide +kernel

theorem W.c4 : ckW (nat_lit 4) = true := by
  rw [ckW_eq]
  decide +kernel

end CFSG.KD.B45.C260393

end
