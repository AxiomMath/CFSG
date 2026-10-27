module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi23TwistDefs
import Certificates.Kernel.Fi23Nt.GlueC

public section

namespace Certificates

open CertificateChecks

theorem certificate101701 : 
    CFSG.LocalAnalysis.GLTheoremA.H1017.Fi23Twist.FactB ∧
      CFSG.LocalAnalysis.GLTheoremA.H1017.Fi23Twist.FactC :=
  ⟨KernelFi23Nt.factB_k, KernelFi23Nt.factC_k⟩

end Certificates
