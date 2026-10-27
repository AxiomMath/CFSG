module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaCheck
import Certificates.Kernel.Sporadic.OddCore.C24600F
import Certificates.Certificate2233
import Certificates.Certificate2234
import Certificates.Certificate2278
import Certificates.Certificate2280
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace Certificates

open CertificateChecks

theorem certificate24600 : CFSG.EvenSporadicStandard.Fin76b.Beta.j2CountComm = 1080 ∧
    CFSG.EvenSporadicStandard.Fin76b.Beta.j2CountSq = 0 :=
  ⟨KernelSpor.C24600.countComm, KernelSpor.C24600.countSq⟩

end Certificates
