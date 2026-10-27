module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneInputs

public section

namespace CertificateChecks.KernelCo1B.H24510

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native
  CFSG.EvenSporadicStandard.TwoCo1.HypOne

def dPA : List Rows × List Rows × Bool :=
  dag (brayElts (brayRows iotaARows twoAD1) twoABray) perfPA

def dUA : List Rows × List Rows × Bool := dag (pickRows dPA perfPIdxA) perfUA

def dFA : List Rows × List Rows × Bool := dag (commRows dUA perfCIdxA) perfFA

def dQA : List Rows × List Rows × Bool := dag (pickRows dPA perfPIdxA) perfQA

end CertificateChecks.KernelCo1B.H24510

end
