module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieCross
meta import YardstoneContract
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import YardstoneContract

public section

namespace CFSG.Yardstones.Statements

@[expose] def Y600f261da4e2dd4f : Prop :=
  yardstone_type% CFSG.AGLEmbeddingD2.KFactSeitzRankTwo

end CFSG.Yardstones.Statements
