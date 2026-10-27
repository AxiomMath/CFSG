module

public import CFSG.Quasithin.Background.HMathieuNormInputs
import Certificates.Kernel.MathieuAut.Checks7065

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.Blueprint in
theorem certificate7065 :
    inAutOK m23AArr = true ∧ inAutOK m23BArr = true :=
  KernelMathieuAut.m23ArrsK

end Certificates
