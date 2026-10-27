module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThListFacts
public import Certificates.Certificate1022
import Certificates.Kernel.ThCent.R7Glue
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs
public import CFSG.Perm.CentralizerOrbit
public import CFSG.Sporadic.Ly.ThreeBCount
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.Th.KernelContractBase
public import CFSG.Sporadic.ThSchreier.FullAutCoreBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase1

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Th CFSG.HardMathSupport.Timmesfeld.SporadicBalance in
theorem certificate17303 : 
    (∃ i < 1176, orderOf (ThList.el7 i) = 4) ∧
      ∀ i < 1176, ThList.el7 i * ThSlp.slpJ a b ThSevenNative.prog7 25 =
        ThSlp.slpJ a b ThSevenNative.prog7 25 * ThList.el7 i → ThList.el7 i ^ 7 = 1 :=
  KernelThList.th_rank7

end Certificates
