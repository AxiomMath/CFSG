
module


public import CFSG.Certificates.Kernel.Th.SoundnessMax3
import Certificates.Kernel.Th.Max3

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.PresentationLocal CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3
  CFSG.Sporadic.Th.Max3.AltQuot in
theorem certificate10091 :
    (∀ k : CarmichaelIndex 9,
        eqRows (powRows (carmRows k) 3) (rowsNfIdx (carmCubeIdx k)) = true) ∧
      (∀ j k : CarmichaelIndex 9, j.1 < k.1 →
        eqRows (powRows (mulRows (carmRows j) (carmRows k)) 2) (rowsNfIdx (carmPairIdx j k)) =
          true) ∧
      eqRows (mulRows rowsX waRows) (rowsNfIdx 299) = true ∧
      eqRows (mulRows (powRows rowsY 5) wbRows) (rowsNfIdx 201) = true ∧
      eqRows rowsCommXQ idRows = false ∧ eqRows rowsCommXQ rowsZ = false :=
  CFSG.KC.Th.Soundness.max3_sound10091 KernelTh.max3Data KernelTh.max3_hA KernelTh.max3_hB
    KernelTh.max3_ok

end Certificates
