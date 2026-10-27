
module

public import Certificates.Certificate7162Base

public import CFSG.Quasithin.Vol2.KGFactG2RuInputs
public meta import CFSG.Quasithin.Vol2.KGFactG2RuInputs
import CFSG.Sporadic.Schreier.RuCheckBasicInputs
import CFSG.Sporadic.Schreier.RuCheckInvInputs
meta import CFSG.Sporadic.Schreier.RuTreeEltA
meta import CFSG.Sporadic.Schreier.RuWitArrays
meta import CFSG.Sporadic.Schreier.RuCheckChains
meta import CFSG.Sporadic.Schreier.RuEnum
import Certificates.Kernel.SporSch.Ru.E64

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.H13.Ch4.G2Ru in
theorem certificate7162 : g2E64Check = true := KernelSporSch.RuE64.e64Check

end Certificates
