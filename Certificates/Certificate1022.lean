
module

public import Certificates.Certificate1022Base

public import CFSG.Certificates.Kernel.Th.SoundnessBase
import Certificates.Kernel.Th.Seed

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Matrix in
theorem certificate1022 : (
 eqRows (CFSG.Sporadic.Th.Native.mulRows (CFSG.Sporadic.Th.Native.rowsOf seedA) (CFSG.Sporadic.Th.Native.rowsOf seedA)) idRows = true 
)
    ∧ (

    eqRows (CFSG.Sporadic.Th.Native.mulRows (CFSG.Sporadic.Th.Native.mulRows (CFSG.Sporadic.Th.Native.rowsOf seedB) (CFSG.Sporadic.Th.Native.rowsOf seedB)) (CFSG.Sporadic.Th.Native.rowsOf seedB)) idRows = true 
)
    ∧ (

    eqRows (CFSG.Sporadic.Th.Native.mulRows (CFSG.Sporadic.Th.Native.mulRows (transposeRows (CFSG.Sporadic.Th.Native.rowsOf seedA)) fcRows) (CFSG.Sporadic.Th.Native.rowsOf seedA)) fcRows =
      true 
)
    ∧ (

    eqRows (CFSG.Sporadic.Th.Native.mulRows (CFSG.Sporadic.Th.Native.mulRows (transposeRows (CFSG.Sporadic.Th.Native.rowsOf seedB)) fcRows) (CFSG.Sporadic.Th.Native.rowsOf seedB)) fcRows =
      true 
) :=
  CFSG.KC.Th.Soundness.seed_sound KernelTh.seedData KernelTh.seed_hA KernelTh.seed_hB
    KernelTh.seed_ok

end Certificates
