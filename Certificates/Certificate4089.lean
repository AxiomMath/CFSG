module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporWitCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHSLit
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHSCheckInputs
import Certificates.Kernel.LocalQT.HS4089.G

public section

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.HSPairs in
open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.HS CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2 CFSG.Blueprint in
open CFSG.Sporadic.HS.Native (hsData) in
theorem certificate4089 : (OmegaSpec ptAct hsL1.toArray hsDelta hsOm1 ∧ hsOm1.lbl.size = 15 ∧
            Wit3Ok hsData.n ptAct hsL1 hsOm1.lbl.toList b31 q31a q31b ∧
            WitPOk hsData.n ptAct hsL1 hsOm1.lbl.toList 5 b51 q51) ∧
          (OmegaSpec ptAct hsL2.toArray hsDelta hsOm2 ∧ hsOm2.lbl.size = 21 ∧
            Wit3Ok hsData.n ptAct hsL2 hsOm2.lbl.toList b32 q32a q32b ∧
            WitPOk hsData.n ptAct hsL2 hsOm2.lbl.toList 7 b72 q72) :=
  CFSG.KD.LQT.H4089.facts

end Certificates
