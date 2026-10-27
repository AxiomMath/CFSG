module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2MinusW
import Certificates.Kernel.OmegaEight.MinusChecksA
import Certificates.Kernel.OmegaEight.MinusChecksB
import Certificates.Kernel.OmegaEight.MinusChecksS
import Certificates.Kernel.OmegaEight.MinusChecksSecond
import Certificates.Kernel.OmegaEight.MinusChecksM2
import Certificates.Kernel.OmegaEight.MinusChecksCand

public section

namespace Certificates

open CertificateChecks.KernelO8 in
open CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.Stage2.Minus in
theorem certificate3411 : ∃ W : MinusW.Wit, (MinusW.cCheck W = true)
    ∧ (MinusW.tcCheck W = true)
    ∧ (MinusW.uCheck W = true)
    ∧ (MinusW.m2Check W = true)
    ∧ (MinusW.offCheck W = true)
    ∧ (MinusW.phiCheck W = true)
    ∧ (MinusW.c2Check W = true)
    ∧ (MinusW.p3Check W = true)
    ∧ (MinusW.candChk W = true)
    ∧ (MinusW.brayChk W 2 CFSG.EvenSmallLie.OmegaEight.Stage2.Minus.brayProg2 CFSG.EvenSmallLie.OmegaEight.Stage2.Minus.brayOut2 = true)
    ∧ (MinusW.brayChk W 3 CFSG.EvenSmallLie.OmegaEight.Stage2.Minus.brayProg3 CFSG.EvenSmallLie.OmegaEight.Stage2.Minus.brayOut3 = true)
    ∧ (MinusW.brayChk W 4 brayProg4 brayOut4 = true)
    ∧ (MinusW.brayChk W 5 brayProg5 brayOut5 = true)
    ∧ (MinusW.brayChk W 6 CFSG.EvenSmallLie.OmegaEight.Stage2.Minus.brayProg6 CFSG.EvenSmallLie.OmegaEight.Stage2.Minus.brayOut6 = true)
    ∧ (MinusW.sChk0 W = true)
    ∧ (MinusW.sChk1 W = true)
    ∧ (MinusW.secondChk W = true)
    ∧ (MinusW.no8Chk W = true) :=
  ⟨wM, c_okM, tc_okM, u_okM, m2_okM, off_okM, phi_okM, c2_okM, p3_okM, cand_okM, bray2_okM,
    bray3_okM, bray4_okM, bray5_okM, bray6_okM, s0_okM, s1_okM, second_okM, no8_okM⟩

end Certificates
