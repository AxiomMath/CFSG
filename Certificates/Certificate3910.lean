module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitPlusW
import Certificates.Kernel.OmegaEight.N3PChecksA
import Certificates.Kernel.OmegaEight.N3PChecksB
import Certificates.Kernel.OmegaEight.N3PChecksM2
import Certificates.Kernel.OmegaEight.N3PChecksCand
import Certificates.Kernel.OmegaEight.N3PChecksS
import Certificates.Kernel.OmegaEight.N3PChecksS2
import Certificates.Kernel.OmegaEight.N3PChecksNC

public section

namespace Certificates

open CertificateChecks.KernelO8 in
open CFSG.EvenSmallLie.OmegaEight.N3Split CFSG.EvenSmallLie.OmegaEight.N3Split.Plus in
theorem certificate3910 : ∃ W : PlusW.Wit, (PlusW.cCheck W = true)
    ∧ (PlusW.tcCheck W = true)
    ∧ (PlusW.ukCheck W = true)
    ∧ (PlusW.m2Check W = true)
    ∧ (PlusW.offCheck W = true)
    ∧ (PlusW.phiCheck W = true)
    ∧ (PlusW.c2Check W = true)
    ∧ (PlusW.p3Check W = true)
    ∧ (PlusW.candChk W = true)
    ∧ (PlusW.brayChk W 2 brayProg2 brayOut2 = true)
    ∧ (PlusW.brayChk W 3 brayProg3 brayOut3 = true)
    ∧ (PlusW.sChk0 W = true)
    ∧ (PlusW.tauChk0 W = true)
    ∧ (x0Chk = true)
    ∧ (PlusW.s2Chk W = true)
    ∧ (PlusW.sChk1 W = true)
    ∧ (PlusW.tauChk1 W = true)
    ∧ (zChk = true)
    ∧ (PlusW.noChk W = true)
    ∧ (PlusW.ncChk W = true) :=
  ⟨wN3P, c_okN3P, tc_okN3P, uk_okN3P, m2_okN3P, off_okN3P, phi_okN3P, c2_okN3P, p3_okN3P,
    cand_okN3P, bray2_okN3P, bray3_okN3P, s0_okN3P, tau0_okN3P, x0_okN3P, s2_okN3P, s1_okN3P,
    tau1_okN3P, z_okN3P, no_okN3P, nc_okN3P⟩

end Certificates
