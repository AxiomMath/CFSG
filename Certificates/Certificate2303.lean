module

public import CFSG.Sporadic.SuzOddCore.OddCoreCheckInputs
public meta import CFSG.Sporadic.SuzOddCore.InvTCheck
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
import Certificates.Kernel.Sporadic.OddCore.Suz2303F

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
open CFSG.PSL3Four.Native in
theorem certificate2303 : (oddEntryOK 0 = true)
    ∧ (oddEntryOK 1 = true)
    ∧ (oddEntryOK 2 = true)
    ∧ (oddEntryOK 3 = true) := KernelSpor.OddCore.facts2303

end Certificates
