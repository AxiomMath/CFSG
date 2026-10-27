module

public import CFSG.ClassicalInvolution.SmallCases.NobqL34CheckInputs
import Certificates.Kernel.LocalComp.L34Key.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Nobq in
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four in
theorem certificate9304 : (l34CQ = true)
    ∧ (l34Key = true) :=
  ⟨KernelLC.L34Key.l34CQ_true, KernelLC.L34Key.l34Key_true⟩

end Certificates
