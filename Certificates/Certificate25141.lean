module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataModTripleNative
import Certificates.Kernel.J4Q.Orbits

public section

namespace CertificateChecks.Batch25141

open CFSG.EvenSporadicStandard.J4Std.DataMod

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
theorem chkTriple_true : chkTriple = true := by
  unfold chkTriple
  rw [CertificateChecks.KernelJ4Q.tMasks_eq]
  decide +kernel

end CertificateChecks.Batch25141

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.J4Std.DataMod in
theorem certificate25141 : chkTriple = true := CertificateChecks.Batch25141.chkTriple_true

end Certificates
