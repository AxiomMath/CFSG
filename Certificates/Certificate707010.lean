module

public import Certificates.Data.TriD4Phi
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Link
import Certificates.Kernel.D4.PhiFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.AGLEmbedding.ChevOuter
  CFSG.StandardType.TriD4TwoRow in
theorem certificate707010 : (∀ i : Fin 2457, lineCert.pts[(d4Phi i : ℕ)]! = frobCode lineCert.pts[(i : ℕ)]!) ∧
    CFSG.Monster.B.Co2.Rep 2457 (phiArr ()) d4Phi ∧ d4Phi ^ 3 = 1 ∧
    ∀ k < 18,
      d4Phi * d4Rho (letterX k) = d4Rho (letterX (sg k)) * d4Phi :=
  KernelD4.phi_facts

end Certificates
