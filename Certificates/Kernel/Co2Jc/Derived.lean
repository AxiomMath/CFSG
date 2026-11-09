module

public import CFSG.Sporadic.Co2Jc.Native.Derived

public import Certificates.Data.Kernel.RangeSplit
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxHeartbeats 0

namespace CertificateChecks.KernelCo2Jc

open CFSG.KC.RangeSplit CFSG.Sporadic.Co2Jc CFSG.Sporadic.Co2Jc.Native CFSG.Sporadic.Co2Jc.Data

theorem derived_check_orderOK : CFSG.Sporadic.Co2Jc.Native.orderOK = true := by quickRfl

theorem derived_check_conj0 : ((List.range 2).all fun i =>
    wordOK ([0] ++ gwList[i]! ++ invW[0]!) (dWord ((conjD[0]!)[i]!))) = true := by
  quickRfl

theorem derived_check_conj1 : ((List.range 2).all fun i =>
    wordOK ([1] ++ gwList[i]! ++ invW[1]!) (dWord ((conjD[1]!)[i]!))) = true := by
  quickRfl

theorem derived_check_conj2 : ((List.range 2).all fun i =>
    wordOK ([2] ++ gwList[i]! ++ invW[2]!) (dWord ((conjD[2]!)[i]!))) = true := by
  quickRfl

theorem derived_check_conjOK : CFSG.Sporadic.Co2Jc.Native.conjOK = true := by
  unfold conjOK
  refine List.all_eq_true.2 fun k hk => ?_
  have h := List.mem_range.1 hk
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  exacts [derived_check_conj0, derived_check_conj1, derived_check_conj2]

theorem derived_check_elemOK : CFSG.Sporadic.Co2Jc.Native.elemOK = true := by quickRfl

theorem derived_check_pullOK : CFSG.Sporadic.Co2Jc.Native.pullOK = true := by quickRfl

theorem derived_check_signOK : CFSG.Sporadic.Co2Jc.Native.signOK = true := by quickRfl

theorem derived_check_maskOK : CFSG.Sporadic.Co2Jc.Native.maskOK = true := by quickRfl

theorem derived_check : CFSG.Sporadic.Co2Jc.Native.derivedOK = true := by
  unfold CFSG.Sporadic.Co2Jc.Native.derivedOK
  exact andT (andT (andT (andT (andT derived_check_orderOK derived_check_conjOK) derived_check_elemOK) derived_check_pullOK) derived_check_signOK) derived_check_maskOK

end CertificateChecks.KernelCo2Jc
