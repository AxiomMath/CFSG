module

public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheck
public import CFSG.Monster.B.Fischer.Fi22OuterCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCheck
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheck
import Certificates.Kernel.Sporadic.Fi22.Ext2073

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Co2.Native in
open CFSG.Monster.B.Fischer in
theorem certificate2073 : eqA 3510 (fi22ExtArr 23) (fi22OuterStrong3510 1)[0]! = true := KernelSpor.Fi22E2073.facts

end Certificates
