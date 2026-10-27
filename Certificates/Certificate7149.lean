module

public import CFSG.Quasithin.Vol2.KGFactE64HeData
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHeInputs
import Certificates.Kernel.He7149.Final
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRep
public import CFSG.Sporadic.He
public import CFSG.Sporadic.Th.F2Spec
public import Certificates.Certificate113

public section

namespace Certificates

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.He
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H13.KGE64 in
theorem certificate7149 : e64Check 8330 heB ptAct heE64Lt heE64Y heE64O heLabels7 = true :=
  CFSG.KD.He7149.e64

end Certificates
