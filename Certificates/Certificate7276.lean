module

public import Certificates.Data.ASVolIK43
import Certificates.Kernel.ASVolI.K43Checks7276
import CFSG.Certificates.Kernel.ASVolI.K43Sound

public section

namespace Certificates

open CertificateChecks

theorem certificate7276 :
    CFSG.ASVolI.K43Data.octOK () = true ∧
    CFSG.ASVolI.K43Data.ptChainOK () = true ∧
    CFSG.ASVolI.K43Data.vecChainOK () = true :=
  ⟨CFSG.KS.ASVolI.octOK_of_K KernelASVolI.k43_octOKK,
    CFSG.KS.ASVolI.ptChainOK_of_K KernelASVolI.k43_ptChainK,
    CFSG.KS.ASVolI.vecChainOK_of_K KernelASVolI.k43_vecChainK⟩

end Certificates
