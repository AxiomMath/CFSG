module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalTab
import Certificates.Certificate9441
import Certificates.Kernel.Sp62W.ChecksDC
import CFSG.Certificates.Kernel.Sp62W.Cosets

public section

open CFSG.AGLEmbedding.KFactProofs.Sp62Local

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two in
theorem certificate9443 : ∀ x : H6, x ∈ Hgen gensWD ∨
    ∃ w ∈ Hgen gensWD, ∃ w' ∈ Hgen gensWD, x = w * elt cG1 * w' :=
  CFSG.KC.Sp62W.double_cosets
    (tabCheck_spec (gens := gensWD) (n := 51840) (P := propWD) certificate9441.1).2.2.1
    KernelSp62W.ch9443dc

end Certificates
