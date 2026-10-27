module

public import Certificates.Kernel.Co1B.Data17325
public import Certificates.Data.Kernel.SporSch.Co1BfsSeg
public import CFSG.Certificates.Kernel.Common.EachTrue
public import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17325

open CFSG.KS.SporSch.M24 (gtHeadK gtSegK)

@[expose] noncomputable def EM (l : Nat) : Nat := DB.M (Nat.add 87 l)

theorem kETh : gtHeadK ET.P ET.PAR ET.LAB ET.N 1000 36 = true := by quickRfl

#kc_each CertificateChecks.KernelCo1B.Bound17325.tr17325 s
  (fun i => gtSegK EM 4 40000 ET.N ET.P ET.PAR ET.LAB ET.W ET.S 1000 i) 0 36

#kc_forall_chunks kETs (fun i => gtSegK EM 4 40000 ET.N ET.P ET.PAR ET.LAB ET.W ET.S 1000 i = true)
  36 CertificateChecks.KernelCo1B.Bound17325.tr17325.s 1

end CertificateChecks.KernelCo1B.Bound17325

end
