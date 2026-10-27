module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.NativeFactsInputs
public import CFSG.Monster.B.CTIB.HOuter
public import CFSG.Monster.B.GSide.HInnerFusion
public import CFSG.LocalAnalysis.EvenSmallLie.FoursGroup
import Certificates.Kernel.TwoE6.FourGroup
import Certificates.Data.Kernel.CTIBqBind
import Certificates.Kernel.TwoE6.CTIBqData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.TwoE6 in
theorem certificate3128 : CFSG.EvenSmallLie.TwoE6.fgOK = true := KernelTwoE6.cert3128

end Certificates
