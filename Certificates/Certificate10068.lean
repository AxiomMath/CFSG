module

public import CFSG.Sporadic.Co1.Module.CoTwoNortonDataInputs
import Certificates.Kernel.Co1M.C10068
public import CFSG.Sporadic.Co1.Module.PairsCheckInputs

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co1.CoTwoNative CFSG.Sporadic.Co1.Module.CoTwo CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.Module in
theorem certificate10068 :
    (nortonCheck 22 genRows nortonCert = true)
    ∧ (repCheck (transposeRows 24 qRows) (transposeRows 24 f0Rows) r1Rows r2Rows
      wRows mt1 mt2 2 359217 = true)
    ∧ (Pairs.inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280
      359217 = true) := KernelCo1M.c10068

end Certificates
