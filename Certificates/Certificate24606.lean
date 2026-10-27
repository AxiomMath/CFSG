module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.PinEJ2Check
import Certificates.Kernel.J2Cover.M22Bind
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Fin76b.J2

theorem certificate24606 : CFSG.EvenSporadicStandard.Fin76b.J2.j2PinCheck = true := by
  have e : mulJ2 = KernelJ2Cover.mtK := KernelJ2Cover.mt_eq
  rw [j2PinCheck, e]
  quickRfl

end Certificates
