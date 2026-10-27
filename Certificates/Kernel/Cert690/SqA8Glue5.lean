module

public import Certificates.Kernel.Cert690.SqA8Glue
public import Certificates.Kernel.Cert690.SqA8Sel
public import Certificates.Kernel.Cert690.SqA8Cnt
public import CFSG.Certificates.Kernel.Cert690.SqA8S5Sound

public section

namespace CertificateChecks.KernelC690.SqPass

open CFSG.KC.C690 CFSG.GF2Type.Smith1979W3.Cert690

theorem a8S5P : a8S5Of (a8Data ()) = true := a8Hyp.s5 selOm cmOm cntOK

theorem a8SquareP : a8SquareCheck () = true := by
  unfold a8SquareCheck
  dsimp only
  rw [a8S1P, a8S2P, a8S3P, a8S4P, a8S5P]
  rfl

end CertificateChecks.KernelC690.SqPass

end
