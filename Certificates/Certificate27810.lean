module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYData
import Certificates.Certificate2236
import Certificates.Kernel.Sporadic.OddCore.S16J2F27810
import Certificates.Kernel.Sporadic.OddCore.S16J3F27810
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace Certificates

open CertificateChecks

theorem certificate27810 : CFSG.EvenSporadicStandard.Fin76b.S16.j2S16OK = true ∧
    CFSG.EvenSporadicStandard.Fin76b.S16.j3S16OK = true :=
  ⟨KernelSpor.S16J2.j2, KernelSpor.S16J3.j3⟩

end Certificates
