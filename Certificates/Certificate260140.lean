module

public import Certificates.Data.SmithB42TitsDisp
import Certificates.Kernel.SporSch.Tits.Disp260140

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.B42Tits in
theorem certificate260140 : titsOrderCheck = true ∧ titsColourCheck = true ∧ titsColourACheck = true := KernelSporSch.TitsDisp.facts

end Certificates
