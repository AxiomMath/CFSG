module

public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicMcLW
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicMcLW
public meta import Certificates.Kernel.Sporadic.RawGen
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public meta import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensusW
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensusW
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.Monster.Code.Weights
public import CFSG.Monster.Code.Weights
public import CFSG.RankThree.Native.HSMcLSmallCheck
public meta import CFSG.RankThree.Native.HSMcLSmallCheck

public section

namespace CertificateChecks.KernelCensus.McLK

@[expose] def mclDW : List (List Int) := CFSG.Sporadic.Schreier.mclWords.toList.drop 2

end CertificateChecks.KernelCensus.McLK

end

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelCensus.McLS CFSG.Sporadic.Schreier.mclStrongHex
#kmisc_hexflat CertificateChecks.KernelCensus.McLS CFSG.Sporadic.Schreier.mclStrongHex 4 275 9 13

#ks_rawchain CertificateChecks.KernelCensus.McLC 275 9 55
  CFSG.Sporadic.Schreier.mclStrongArrs
  CFSG.Sporadic.Schreier.PairMcL.baseArr 2
  CertificateChecks.KernelCensus.McLK.mclDW
