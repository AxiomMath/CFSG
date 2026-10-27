module

public import CFSG.ClassicalInvolution.SmallCases.NobqMcLInputs
import Certificates.Kernel.Sporadic.OddCore.McLNobqF
public import Certificates.Certificate9314

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Nobq in
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.ClassicalInvolution.McLData CFSG.ClassicalInvolution.McLProof in
theorem certificate9307 : noncentralInvOK = true := KernelSpor.McLNobq.facts9307

end Certificates
