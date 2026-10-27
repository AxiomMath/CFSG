module

public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM23W
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM23W
public meta import Certificates.Kernel.Sporadic.RawGen
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
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCensusW
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCensusW
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.Monster.Code.Weights
public meta import CFSG.Monster.Code.Weights
public meta import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public meta import CFSG.Sporadic.SmallOddCore.CheckSpec
public import Certificates.Kernel.Sporadic.RawGen

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelCensus.M23C 23 5 16
  CFSG.ComponentClassification.RankTwoSporadic.M23.m23SW
  CFSG.ComponentClassification.RankTwoSporadic.M23.m23BaseW 2
  CFSG.ComponentClassification.RankTwoSporadic.M23.m23DW

end
