module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.FrameCheck
import Certificates.Kernel.MinusFrame.ArrFacts

public section

open CFSG.OddTranspositions.PartThree.MinusFrame CertificateChecks.KernelMinusFrame

namespace Certificates

open CFSG.OddTranspositions.PartThree.MinusFrame in
theorem certificate1383012 : frameCheck () = true := by
  unfold frameCheck
  dsimp only
  rw [t0Chk, t0Sub, frameMem, kFrameCommute, cent, l0Chk, aChk, stab, card, notMem, notMul, conjX]
  rfl

end Certificates
