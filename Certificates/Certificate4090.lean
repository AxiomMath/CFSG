module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporWitCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHeWitInputs
import Certificates.Kernel.LocalQT.He4090.G
import Certificates.Kernel.LocalQT.He4090.L
import Certificates.Kernel.He4049.T
import Certificates.Data.Kernel.Spor.PEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.HePairs in
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.He CFSG.QuasithinUnique.K1.SporadicPerm in
theorem certificate4090 : (CntOk 8330 ptAct heL2 heLabels2 r2a r2b q2s ∧
          Wit3Ok 8330 ptAct heL7 heLabels7 b7a q7a q7b ∧
          WitPOk 8330 ptAct heL7 heLabels7 7 b7p q7p) :=
  ⟨CFSG.KD.LQT.H4090.cnt, CFSG.KD.LQT.H4090.wit3, CFSG.KD.LQT.H4090.witP⟩

end Certificates
