module

public import CFSG.Sporadic.Schreier.ONActionData
public import Certificates.Data.CFSGNative.ONSchreier.Vectors
import Certificates.Kernel.Sporadic.ONVec.Vector
import Certificates.Kernel.Sporadic.ONLine.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.F3.Native in
theorem certificate2217 : (vectorCert (digitsW Data.rootDigits) Data.spanIdx (rowsOf 154 Data.spanInvPayload)
      (rowsOf 154 Data.formPayload) Data.baseList Data.strongWords 3 = true
    )
    ∧ (lineCert (digitsW Data.rootDigits) 122760 3 = true) :=
  ⟨KernelSpor.ONVec.vector_cert_proved, KernelSpor.ONLine.line_cert_ok⟩

end Certificates
