module

public import CFSG.Quasithin.Background.HMathieuM21Inputs
import CFSG.Certificates.Kernel.Spor.MathieuSound
import Certificates.Kernel.MathieuFam.Checks7064

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.Blueprint in
open CFSG.Sporadic.Mathieu CFSG.Sporadic.Mathieu.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native in
open scoped commutatorElement in
theorem certificate7064 :
    (check 21 m21Data = true)
    ∧ (inAutOK m21AArr = true ∧ inAutOK m21BArr = true) :=
  ⟨CFSG.KS.Mathieu.mcheck_sound (by decide) KernelMathieuFam.m21K, KernelMathieuFam.m21ArrsK⟩

end Certificates
