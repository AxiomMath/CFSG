module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabA2CheckInputs
import Certificates.Kernel.LocalQT.TabA2.F4043

public section

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519 CFSG.QuasithinUnique.Id2519.Tab CFSG.QuasithinUnique.Id2519.Tab.A2 in
open CFSG.PSL3Four CFSG.PSL3Four.Native in
theorem certificate4043 : (scanU1 = true)
    ∧ (scanU2 = true)
    ∧ (scanU3 = true)
    ∧ (scanPU = true)
    ∧ (scanR = true)
    ∧ (scanA0 = true)
    ∧ (scanTrans = true)
    ∧ (scanZ = true)
    ∧ (scanRed = true)
    ∧ (scanWit = true) :=
  ⟨CFSG.KD.LQT.TA.scanU1_true, CFSG.KD.LQT.TA.scanU2_true, CFSG.KD.LQT.TA.scanU3_true,
    CFSG.KD.LQT.TA.scanPU_true, CFSG.KD.LQT.TA.scanR_true, CFSG.KD.LQT.TA.scanA0_true,
    CFSG.KD.LQT.TA.scanTrans_true, CFSG.KD.LQT.TA.scanZ_true, CFSG.KD.LQT.TA.scanRed_true,
    CFSG.KD.LQT.TA.scanWit_true⟩

end Certificates
