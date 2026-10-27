module

public import CFSG.Sporadic.SuzRecog.ChartTransferTests
import Certificates.Kernel.Sporadic.OddCore.SuzChart

public section

namespace Certificates

open CertificateChecks

theorem certificate15111 : CFSG.Sporadic.SuzRecog.RigidL2.chartSwapOK = true := KernelSpor.SuzChart.facts15111

end Certificates
