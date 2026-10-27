module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineJTwoCertData
import Certificates.Kernel.Sporadic.OddCore.J2EAChecks
public import CFSG.Sporadic.SmallOddCore.J2CheckInputs

public section

namespace Certificates

open CertificateChecks

open CFSG.SeitzReduction.SporadicRefine CFSG.Sporadic.SmallOddCore in
theorem certificate3966 : (idxClosedOK 315 j2SylEnum j2EAIdxOne = true)
    ∧ (idxClosedOK 315 j2SylEnum j2EAIdxTwo = true)
    ∧ (eaCountOK 315 j2Sift j2SylEnum j2EAIdxOne j2EAIdxTwo = true)
    ∧ (eaSupportOK 315 j2Sift j2SylEnum j2EAIdxOne j2EAIdxTwo = true) := KernelSpor.J2EA.cert3966

end Certificates
