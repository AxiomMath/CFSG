
module

public import Certificates.Certificate2177Base

public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
import Certificates.Kernel.SporSch.J4S.Orbits

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier in
theorem certificate2177 : (bfsOK xyGens 1 1771 orb1 = true)
    ∧ (bfsOK xyGens 14 276 orb14 = true)
    ∧ (coverCheck = true)
    ∧ (closedOK xyInvGens orb1.1 1771 = true)
    ∧ (closedOK xyInvGens orb14.1 276 = true)
    ∧ (fixCheck = true)
    ∧ (bfsOK gens1 2 1440 orbB = true)
    ∧ (bfsOK gens2 4 96 orbC = true) := KernelSporSch.J4Orbits.facts

end Certificates
