module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaCheck
import Certificates.Kernel.Sporadic.OddCore.Beta24601F
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace Certificates

open CertificateChecks

theorem certificate24601 : CFSG.EvenSporadicStandard.Fin76b.Beta.j2BetaOK = true ∧
    CFSG.EvenSporadicStandard.Fin76b.Beta.j2MemOK = true :=
  ⟨KernelSpor.B24601.facts24601a, KernelSpor.B24601.facts24601b⟩

end Certificates
