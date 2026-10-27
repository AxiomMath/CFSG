module

public import CFSG.Sporadic.SmallOddCore.J2LocalCheckInputs
public meta import CFSG.Sporadic.SmallOddCore.J2Check
public meta import CFSG.Sporadic.SmallOddCore.LocalCheck
import Certificates.Kernel.Sporadic.OddCore.J2LocF

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native in
theorem certificate2280 : (j2DOK = true)
    ∧ (j2QOK = true)
    ∧ (commTT 315 (wordTbl 315 j2C1Gens [3, 2]) (wordTbl 315 j2C1Gens [2, 4, 2, 4]) = false) := KernelSpor.J2Loc.facts2280

end Certificates
