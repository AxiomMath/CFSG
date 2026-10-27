module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaA5Check
import Certificates.Kernel.Sporadic.OddCore.J2BetaA5F
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace Certificates

open CertificateChecks

theorem certificate24604 : CFSG.EvenSporadicStandard.Fin76b.Beta.j2A5OK = true ∧
    CFSG.EvenSporadicStandard.Fin76b.Beta.j2A5MemOK = true :=
  ⟨KernelSpor.J2BetaA5.facts24604a, KernelSpor.J2BetaA5.facts24604b⟩

end Certificates
