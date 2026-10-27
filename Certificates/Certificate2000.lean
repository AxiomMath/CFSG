module

public import CFSG.Literature.GL52ChainInputs
import Certificates.Kernel.Misc.GL52.Valid

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Literature CFSG.Literature.GL52 Matrix CFSG.Certificates CFSG.Sporadic.Th in
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier in
theorem certificate2000 : (glCert.check = true)
    ∧ (List.ofFn glCert.orbitSize = [31, 30, 28, 24, 16]) :=
  ⟨KernelMisc.GL52C.valid, KernelMisc.GL52C.orbitSizes⟩

end Certificates
