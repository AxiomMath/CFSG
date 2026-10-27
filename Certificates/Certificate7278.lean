module

public import Certificates.Data.ASVolIK43
import Certificates.Kernel.HMathieu.T24Glue
import Certificates.Kernel.ASVolI.K43Checks7278
import CFSG.Certificates.Kernel.ASVolI.K43Sound7278

public section

namespace Certificates

open CertificateChecks

theorem certificate7278 :
    CFSG.ASVolI.K43Data.sylOK () = true ∧
    CFSG.ASVolI.K43Data.classOK () = true ∧
    CFSG.ASVolI.K43Data.modOK () = true :=
  ⟨CFSG.KS.ASVolI.sylOK_of_K KernelHMathieu.T24.packed KernelASVolI.k43_sylK,
    CFSG.KS.ASVolI.classOK_of_K KernelHMathieu.T24.packed KernelASVolI.k43_classK,
    CFSG.KS.ASVolI.modOK_of_K KernelHMathieu.T24.packed KernelASVolI.k43_modK⟩

end Certificates
