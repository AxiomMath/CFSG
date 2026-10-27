module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemFi22Check
import Certificates.Kernel.Sporadic.Fi22.TMem27101

public section

namespace Certificates

open CertificateChecks

theorem certificate27101 : CFSG.EvenSporadicStandard.Induction.TMemFi22Cert.tmFi22Check = true := KernelSpor.TMem27101.check

end Certificates
