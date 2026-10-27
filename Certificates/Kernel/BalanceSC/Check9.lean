module

public import Certificates.Kernel.BalanceSC.Data

set_option maxRecDepth 100000

public section

namespace CFSG.KD.BalSC9

open CFSG.KC.BalanceSC

theorem s3 : eqL S3 (rMasks (nat_lit 9) (nat_lit 3)) = true := by decide +kernel
theorem s5 : eqL S5 (rMasks (nat_lit 9) (nat_lit 5)) = true := by decide +kernel
theorem s7 : eqL S7 (rMasks (nat_lit 9) (nat_lit 7)) = true := by decide +kernel

theorem parts3_1 :
    partsOK (nat_lit 9) (nat_lit 3) (nat_lit 1) (nat_lit 64) S3 (tab64 PB) R3_1 = true := by
  decide +kernel
theorem parts3_2 :
    partsOK (nat_lit 9) (nat_lit 3) (nat_lit 2) (nat_lit 64) S3 (tab64 PB) R3_2 = true := by
  decide +kernel
theorem parts3_3 :
    partsOK (nat_lit 9) (nat_lit 3) (nat_lit 3) (nat_lit 64) S3 (tab64 PB) R3_3 = true := by
  decide +kernel
theorem parts5_1 :
    partsOK (nat_lit 9) (nat_lit 5) (nat_lit 1) (nat_lit 64) S5 (tab64 PB) R5_1 = true := by
  decide +kernel
theorem parts7_1 :
    partsOK (nat_lit 9) (nat_lit 7) (nat_lit 1) (nat_lit 64) S7 (tab64 PB) R7_1 = true := by
  decide +kernel

end CFSG.KD.BalSC9

end
