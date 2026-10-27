module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2PlusW
import Certificates.Kernel.OmegaEight.PlusChecksA
import Certificates.Kernel.OmegaEight.PlusChecksB
import Certificates.Kernel.OmegaEight.PlusChecksM2
import Certificates.Kernel.OmegaEight.PlusChecksCand
import Certificates.Kernel.OmegaEight.PlusChecksS4
import Certificates.Kernel.OmegaEight.PlusChecksS5

public section

namespace Certificates

open CertificateChecks.KernelO8 in
open CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.Stage2.Plus in
theorem certificate3410 : ∃ W : PlusW.Wit, (PlusW.cCheck W = true)
    ∧ (PlusW.tcCheck W = true)
    ∧ (PlusW.uCheck W = true)
    ∧ (PlusW.m2Check W = true)
    ∧ (PlusW.offCheck W = true)
    ∧ (PlusW.phiCheck W = true)
    ∧ (PlusW.c2Check W = true)
    ∧ (PlusW.p3Check W = true)
    ∧ (PlusW.candChk W = true)
    ∧ (PlusW.brayChk W 0 brayProg0 brayOut0 = true)
    ∧ (PlusW.brayChk W 1 brayProg1 brayOut1 = true)
    ∧ (PlusW.brayChk W 2 CFSG.EvenSmallLie.OmegaEight.Stage2.Plus.brayProg2 CFSG.EvenSmallLie.OmegaEight.Stage2.Plus.brayOut2 = true)
    ∧ (PlusW.brayChk W 3 CFSG.EvenSmallLie.OmegaEight.Stage2.Plus.brayProg3 CFSG.EvenSmallLie.OmegaEight.Stage2.Plus.brayOut3 = true)
    ∧ (PlusW.brayChk W 6 CFSG.EvenSmallLie.OmegaEight.Stage2.Plus.brayProg6 CFSG.EvenSmallLie.OmegaEight.Stage2.Plus.brayOut6 = true)
    ∧ (PlusW.brayChk W 7 brayProg7 brayOut7 = true)
    ∧ (PlusW.sChk4 W = true)
    ∧ (PlusW.sChk5 W = true) :=
  ⟨wP, c_okP, tc_okP, u_okP, m2_okP, off_okP, phi_okP, c2_okP, p3_okP, cand_okP, bray0_okP,
    bray1_okP, bray2_okP, bray3_okP, bray6_okP, bray7_okP, s4_okP, s5_okP⟩

end Certificates
