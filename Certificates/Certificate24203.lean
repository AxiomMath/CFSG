module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.OrbitData
import Certificates.Kernel.ThBfs.GlGlue

public section

namespace Certificates

open CertificateChecks

theorem certificate24203 : CFSG.EvenSporadicStandard.ThStd.LocalDataTh.GLFacts = true :=
  KernelThBfs.glFacts

end Certificates
