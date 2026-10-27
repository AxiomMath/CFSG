module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThListFacts
public import Certificates.Certificate1022
import Certificates.Kernel.ThCent.C5Glue
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
theorem certificate17304 : 
    (∀ i < 3000, ∀ q ∈ Subgroup.closure
        ({ThSlp.slpJ a b ThFiveNative.prog5 94, ThSlp.slpJ a b ThFiveNative.prog5 105} : Set ↥J),
      ThList.el5 i * q * (ThList.el5 i)⁻¹ ∈ Subgroup.closure
        ({ThSlp.slpJ a b ThFiveNative.prog5 94, ThSlp.slpJ a b ThFiveNative.prog5 105} : Set ↥J)) ∧
      ∀ i < 3000, ThList.el5 i * ThSlp.slpJ a b ThFiveNative.prog5 94 =
          ThSlp.slpJ a b ThFiveNative.prog5 94 * ThList.el5 i →
        ThList.el5 i * ThSlp.slpJ a b ThFiveNative.prog5 105 =
          ThSlp.slpJ a b ThFiveNative.prog5 105 * ThList.el5 i →
        ∃ k < 5, ThList.el5 i = ThList.c5 ^ k :=
  KernelThList.th_cent5

end Certificates
