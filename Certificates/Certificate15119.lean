module

public import Certificates.Data.GMS78RuB1Check
public import Certificates.Data.GMS78RuB1SCCheck
import Certificates.Kernel.SporSch.Ru.B1P

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15119 : CFSG.Sporadic.RuSchreier.RuB1.ruB1E8Check = true ∧
    CFSG.Sporadic.RuSchreier.RuB1.ruB1XCheck = true ∧
    CFSG.Sporadic.RuSchreier.RuB1.ruB1SCCheck = true := KernelSporSch.RuB1K.facts

end Certificates
