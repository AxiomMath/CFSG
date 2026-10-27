module

public import Certificates.Data.SmithB45ExcJ4C11
import Certificates.Kernel.J4F2.Comm

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Quasithin.B45Exc in
theorem certificate260381 : eqRows (CFSG.Sporadic.J4.Native.powRows (C11 ()) 11) idRows = true ∧ eqRows (C11 ()) idRows = false ∧
    wfRows (C11 ()) = true := KernelJ4F2.c260381

end Certificates
