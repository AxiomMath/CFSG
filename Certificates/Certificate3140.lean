module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth22DihedralInputs
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth22Native
public import CFSG.Monster.B.GSide.HInnerFusionY3
import Certificates.Kernel.TwoE6.Dihedral
import Certificates.Data.Kernel.CTIBqBind
import Certificates.Kernel.TwoE6.CTIBqData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.TwoE6 in
theorem certificate3140 : d8WitnessOK = true := KernelTwoE6.cert3140

end Certificates
