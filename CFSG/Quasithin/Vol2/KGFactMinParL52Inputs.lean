module

public import CFSG.Literature.GL52ChainInputs
public import Certificates.Data.CFSGNative.SporLat.Build
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import Certificates.Certificate113

public section

namespace CFSG.Quasithin.H13.KGMinPar

open CFSG.Literature.GL52 CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] def l52Incl : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], [1, 2, 4], [2], [1, 2, 3, 4, 8, 9, 11],
    [4], [1, 2, 4, 5, 6, 10, 12], [6], [2, 6, 7, 8, 9, 10, 13], [8], [2, 8, 9], [2, 6, 10],
    [4, 8, 11], [4, 6, 12], [6, 8, 13], [4, 6, 8, 11, 12, 13, 14]]

end CFSG.Quasithin.H13.KGMinPar
