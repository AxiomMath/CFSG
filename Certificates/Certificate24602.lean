module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaCheck
import Certificates.Kernel.Sporadic.OddCore.C24602F
import Certificates.Certificate2236
import Certificates.Certificate2237
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace Certificates

open CertificateChecks

theorem certificate24602 : CFSG.EvenSporadicStandard.Fin76b.Beta.j3CountComm = 1080 :=
  KernelSpor.C24602.countComm

end Certificates
