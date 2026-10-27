
module


public import CFSG.Certificates.Kernel.Th.SoundnessMax3
import Certificates.Kernel.Th.Max3

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3.Packet CFSG.Sporadic.Th.Max3 in
theorem certificate10090 :
    eqRows (signedWordRows coreZWord) rowsZ = true ∧
      ∀ i : Fin 8, eqRows (signedWordRows (coreGeneratorWords i))
        (mulRows (rowsQ i) (powRows rowsZ (qPShift i).val)) = true :=
  CFSG.KC.Th.Soundness.max3_sound10090 KernelTh.max3Data KernelTh.max3_hA KernelTh.max3_hB
    KernelTh.max3_ok

end Certificates
