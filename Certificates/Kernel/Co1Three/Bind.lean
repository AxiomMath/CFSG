module

public import Certificates.Kernel.Co1Three.Data
public import Certificates.Kernel.SporSch.Co1.Rows
public import Certificates.Kernel.SporSch.Co1.ElemDag
public import CFSG.Certificates.Kernel.Spor.BindList
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo1Three

open CFSG.KC.Enum CFSG.KS.Raw

theorem bindA : bindListK 24 24 (TS 0) CertificateChecks.KernelSporSch.Co1Rows.RA.toList = true := by
  quickRfl

theorem bindB : bindListK 24 24 (TS 1) CertificateChecks.KernelSporSch.Co1Rows.RB.toList = true := by
  quickRfl

theorem elemA :
    allN 6 (fun k => Nat.beq (TS (Nat.add k 2)) (CertificateChecks.KernelSporSch.Co1Elem.AF k)) = true := by
  quickRfl

end CertificateChecks.KernelCo1Three

end
