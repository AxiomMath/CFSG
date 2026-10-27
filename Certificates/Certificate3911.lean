module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitMinusW
import Certificates.Kernel.OmegaEight.N3MChecksA
import Certificates.Kernel.OmegaEight.N3MChecksB
import Certificates.Kernel.OmegaEight.N3MChecksM2
import Certificates.Kernel.OmegaEight.N3MChecksCand
import Certificates.Kernel.OmegaEight.N3MChecksS
import Certificates.Kernel.OmegaEight.N3MChecksS2
import Certificates.Kernel.OmegaEight.N3MChecksT
import Certificates.Kernel.OmegaEight.N3MChecksTM
import Certificates.Kernel.OmegaEight.N3MChecksNC

public section

namespace Certificates

open CertificateChecks.KernelO8 in
open CFSG.EvenSmallLie.OmegaEight.N3Split CFSG.EvenSmallLie.OmegaEight.N3Split.Minus in
theorem certificate3911 : ∃ W : MinusW.Wit, (MinusW.cCheck W = true)
    ∧ (MinusW.tcCheck W = true)
    ∧ (MinusW.ukCheck W = true)
    ∧ (MinusW.m2Check W = true)
    ∧ (MinusW.offCheck W = true)
    ∧ (MinusW.phiCheck W = true)
    ∧ (MinusW.c2Check W = true)
    ∧ (MinusW.p3Check W = true)
    ∧ (MinusW.candChk W = true)
    ∧ (MinusW.brayChk2 W = true)
    ∧ (MinusW.sChk0 W = true)
    ∧ (MinusW.tauChk0 W = true)
    ∧ (CFSG.EvenSmallLie.OmegaEight.N3Split.Minus.x0Chk = true)
    ∧ (MinusW.s2Chk W = true)
    ∧ (MinusW.sChk1 W = true)
    ∧ (MinusW.tauChk1 W = true)
    ∧ (CFSG.EvenSmallLie.OmegaEight.N3Split.Minus.zChk = true)
    ∧ (MinusW.noChk W = true)
    ∧ (MinusW.sChk3 W = true)
    ∧ (MinusW.thirdChk W = true)
    ∧ (MinusW.ncChk W = true) :=
  ⟨wN3M, c_okN3M, tc_okN3M, uk_okN3M, m2_okN3M, off_okN3M, phi_okN3M, c2_okN3M, p3_okN3M,
    cand_okN3M, bray2_okN3M, s0_okN3M, tau0_okN3M, x0_okN3M, s2_okN3M, s1_okN3M, tau1_okN3M,
    z_okN3M, no_okN3M, s3_okN3M, third_okN3M, nc_okN3M⟩

end Certificates
