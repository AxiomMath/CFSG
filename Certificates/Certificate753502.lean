module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.AlphaCheck
public import CFSG.Sporadic.Schreier.ONOuterDefs
import Certificates.Kernel.Sporadic.ONPv.Alpha

public section

namespace Certificates

open CertificateChecks

theorem certificate753502 : 
    ∃ α : CFSG.ONSchreier.Pv ≃* CFSG.ONSchreier.Pv,
      α ⟨CFSG.ONSchreier.a0, CFSG.ONSchreier.a0_mem⟩ =
        ⟨CFSG.ONSchreier.evalS CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.alphaWordA,
          CFSG.ONSchreier.evalS_mem _⟩ ∧
      α ⟨CFSG.ONSchreier.a1, CFSG.ONSchreier.a1_mem⟩ = ⟨CFSG.ONSchreier.a1, CFSG.ONSchreier.a1_mem⟩ :=
  ⟨KernelSpor.ONPv.alphaPv, KernelSpor.ONPv.alphaPv_facts⟩

end Certificates
