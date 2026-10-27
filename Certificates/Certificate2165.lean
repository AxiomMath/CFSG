module

public import CFSG.Sporadic.Schreier.J1CertData
public import CFSG.Monster.B.Mathieu.ChainCheck
import Certificates.Kernel.SporSch.J1.Chain2165

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu CFSG.Certificates.Native in
theorem certificate2165 : (J1Certificate.chain.check 3080 = true)
    ∧ (J1Certificate.chain.base = [0, 1, 2])
    ∧ (J1Certificate.chain.orbitSizes 3080 = [3080, 19, 3]) := KernelSporSch.J1.facts

end Certificates
