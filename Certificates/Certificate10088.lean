
module


public import CFSG.Certificates.Kernel.Th.SoundnessMax3
import Certificates.Kernel.Th.Max3

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3.AllConj CFSG.Sporadic.Th.Max3 in
theorem certificate10088 :
    eqRows (mulRows rowsFusionQ0 (rowsQ 0)) (mulRows rowsA rowsFusionQ0) = true ∧
      eqRows (mulRows rowsFusionX rowsX) (mulRows rowsA rowsFusionX) = true :=
  CFSG.KC.Th.Soundness.max3_sound10088 KernelTh.max3Data KernelTh.max3_hA KernelTh.max3_hB
    KernelTh.max3_ok

end Certificates
