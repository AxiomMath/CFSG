module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneData
public import CFSG.Sporadic.Co1Block.CentCheck
public import CFSG.Sporadic.Co1Block.TwoBData

public section

namespace CertificateChecks.KernelCo1B.Syl2B

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native
  CFSG.EvenSporadicStandard.TwoCo1.HypOne

def dagS : List Rows × List Rows × Bool := dag (brayElts (brayRows aR twoBD1) twoBBray) sylD2B

def sgArr : Array (Array Nat) := (sylIdxB.map fun j => dagS.1.getD j one).toArray

end CertificateChecks.KernelCo1B.Syl2B

end
