module

public import Certificates.Data.E68Spor.Chk
public import Certificates.Data.E68Spor.Words
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHeInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificateInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuCertificateInputs
import Certificates.Kernel.E68Spor4215.Final
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

open CFSG.Quasithin.E6.Spor CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.Ch1.SporLat.He CFSG.QuasithinUnique.Ch1.SporLat.RuCert in
open CFSG.Sporadic.Ru.Native (ruData) in
theorem certificate4215 :
    (rChk 8330 ptAct heDelta heSTabsC heTa heTb heSLPC[170]! heUWords heYWord heNWord 7 21 =
        true ∧
      ncChk 8330 heTa heSLPC[170]! = true) ∧
    (rChk ruData.n ptAct ruDelta ruSTabsL ruTaL ruTbL ruSLPL[154]! ruUWords ruYWord ruNWord 5 15 =
        true ∧
      ncChk ruData.n ruTaL ruSLPL[154]! = true) :=
  ⟨CFSG.KD.E68S4215.he_ok, CFSG.KD.E68S4215.ru_ok⟩

end Certificates
