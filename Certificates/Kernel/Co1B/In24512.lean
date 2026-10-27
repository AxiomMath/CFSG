module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneInputs

public section

namespace CertificateChecks.KernelCo1B.H24512

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native
  CFSG.EvenSporadicStandard.TwoCo1.HypOne

def dPC : List Rows × List Rows × Bool :=
  dag (brayElts (brayRows iotaCRows twoCD1) twoCBray) perfPC

def dUC : List Rows × List Rows × Bool := dag (pickRows dPC perfPIdxC) perfUC

def dFC : List Rows × List Rows × Bool := dag (commRows dUC perfCIdxC) perfFC

def dQC : List Rows × List Rows × Bool := dag (pickRows dPC perfPIdxC) perfQC

end CertificateChecks.KernelCo1B.H24512

end
