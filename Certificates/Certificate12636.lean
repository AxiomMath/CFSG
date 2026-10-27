
module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeInputs
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeInputs
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import Certificates.Data.CFSGNative.HeldB.Tests
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
import Certificates.Kernel.Co2Chain.He12636S
import CFSG.Sporadic.HeldB.CertPChainData
import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace Certificates

open CFSG CFSG.Sporadic CFSG.Sporadic.HeldB CFSG.Certificates CFSG.Sporadic.Schreier in
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Native in
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB.Native in
open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.PrimCert in
theorem certificate12636 : ((countWPar 1 (commB heThreeBA heBase)
        (heBlock0.filter fun t0 => heThreeBA[t0[0]!]! == t0[0]!) [heBlock1, heBlock2] == 7560 &&
      countWPar 1 (commB heThreeBB heBase)
        (heBlock0.filter fun t0 => heThreeBB[t0[0]!]! == t0[0]!) [heBlock1, heBlock2] == 504 &&
      countWPar 1 (fun w => CFSG.Sporadic.Schreier.PairNative.fixB heBase w 3) (heBlock0.filter fun t0 => t0[0]! == 0)
        [heBlock1, heBlock2] == 12609) = true) :=
  CertificateChecks.KernelCo2Chain.He12636.blocks

end Certificates
