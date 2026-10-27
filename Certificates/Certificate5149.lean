module

public import CFSG.GH74.Uniqueness.SU.KI1r4F61J3Check
public import CFSG.Sporadic.SmallOddCore.J3Data
public meta import CFSG.GH74.Uniqueness.SU.KI1r4F61J3Check
public meta import CFSG.Sporadic.SmallOddCore.J3Data
import Certificates.Kernel.Sporadic.OddCore.J3FourGen

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallOddCore CFSG.GH74.Uniqueness.SU.K.R4 in
theorem certificate5149 : (j3Rows.all fun r => r.outer == false || fourGenOK 6156 r.centGens 0 1) = true := KernelSpor.OddCore.j3_fourGen

end Certificates
