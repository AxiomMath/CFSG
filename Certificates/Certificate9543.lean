module

public import Certificates.Data.Item434D42
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42LinkCheck
import Certificates.Kernel.D4.LinkFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Monster.B.Fischer in
theorem certificate9543 :
    arrCertOK projAct 18 validV keyV rootV CFSG.RankThree.PartTwo.Sec4.Item434D42.lineCert = true ∧ CFSG.RankThree.PartTwo.Sec4.Item434D42.lineCert.pts.size = 2457 ∧
      eqA 2457 d4GenA (compWord CFSG.RankThree.PartTwo.Sec4.Item434D42.lineCert [2, 5, 10]) = true ∧
      eqA 2457 d4GenB (compWord CFSG.RankThree.PartTwo.Sec4.Item434D42.lineCert [16, 17, 7, 4, 10]) = true ∧
      allLt 18 (fun k => siftA 2457 d4LevelsA d4ChainABaseArr 0 (piArr CFSG.RankThree.PartTwo.Sec4.Item434D42.lineCert k)) = true :=
  ⟨KernelD4.pin.1, KernelD4.pin.2.1, KernelD4.wordA_ok, KernelD4.wordB_ok, KernelD4.siftL_ok⟩

end Certificates
