module

public import Certificates.Data.GH74M12RankCheck
public meta import Certificates.Data.GH74M12RankCheck
import Certificates.Kernel.Sporadic.OddCore.M12SylF
import CFSG.Sporadic.SmallOddCore.ClassSimple
import Certificates.Kernel.Sporadic.OddCore.PEnumGlue3

public section

namespace Certificates

open CertificateChecks

theorem certificate5154 : CFSG.GH74.Generic.S45.EvSpor.m12DataOK = true := KernelSpor.M12Syl.m12_ok

end Certificates
