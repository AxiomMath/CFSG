module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1F0Check
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1DispBCCheck

public section

namespace CertificateChecks.KernelCo1B.C129070

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

def dagF1 : List Rows × List Rows × Bool := brayRows iotaARows f0D1

def dagF2 : List Rows × List Rows × Bool := dag (brayElts dagF1 f0Bidx) f0D2

def dagH : List Rows × List Rows × Bool := dag [aR, bR, iotaARows] dispHeis

def dagC : List Rows × List Rows × Bool := dag [aR, bR, iotaCRows] dispDihD

def dagBC : List Rows × List Rows × Bool := dag [aR, bR, iotaARows] (dispHeis ++ dispBC)

end CertificateChecks.KernelCo1B.C129070

end
