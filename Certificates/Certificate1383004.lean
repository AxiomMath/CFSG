module

public import CFSG.OddTranspositions.PartThree.Eleven.Plus.FrameCheck
import Certificates.Kernel.PlusFrame.FrameFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.OddTranspositions.PartThree.PlusFrame in
theorem certificate1383004 : frameCheck () = true :=
  KernelPlusFr.frame

end Certificates
