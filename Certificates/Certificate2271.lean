module

public import CFSG.Sporadic.SmallOddCore.Co3FusionCheckInputs
public meta import CFSG.Sporadic.SmallOddCore.CentData
public meta import CFSG.Sporadic.Schreier.Co3SylowCheck
import Certificates.Kernel.Sporadic.OddCore.Co3FusF

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier.Co3 in
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native in
theorem certificate2271 : co3FusionOK = true := KernelSpor.Co3Fus.facts2271

end Certificates
