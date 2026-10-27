module

public import Certificates.Data.Item434D42
import Certificates.Kernel.D4.LocalFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.Item434D42 in
theorem certificate9544 :
    CFSG.RankThree.PartTwo.Sec4.Item434D42.localOK 2457 2457 d4Lines[0]! d4CACert.pts d4SelfPtA d4PairWitA = true ∧
      CFSG.RankThree.PartTwo.Sec4.Item434D42.localOK 2457 2457 d4Lines[1]! d4CBCert.pts d4SelfPtB d4PairWitB = true :=
  ⟨KernelD4.local_okA, KernelD4.local_okB⟩

end Certificates
