module

public import Certificates.Data.Item434D42
import Certificates.Kernel.D4.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.RankThree.PartTwo.KFacts.K426
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native CFSG.RankThree.PartOne in
theorem certificate9545 :
    caseChainOK2P 2457 d4ChainBArrs d4ChainBBaseArr d4ChainBWords d4GenA d4GenB = true ∧
      centOKP 3 2457 d4ChainBArrs d4ChainBBaseArr d4Lines[1]! d4RelsB d4CBGens d4Keys d4CBCert
        648 = true :=
  ⟨KernelD4.chainB_ok, KernelD4.caseB_ok⟩

end Certificates
