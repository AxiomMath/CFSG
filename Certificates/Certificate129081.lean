module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2HeisCheck
import Certificates.Kernel.SchreierFam.C129081K

public section

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2 CFSG.KS.MatRep
  CertificateChecks.KernelSporSch.Co2M CertificateChecks.KernelSchreierFam.Co2Slp

namespace Certificates

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2 in
theorem certificate129081 : heisCheck () = true := by
  have hB : RepT 22 CFSG.Sporadic.Co2Cert.co2PackedVecs (heisBase ()) heisT := by
    unfold heisBase heisT
    exact repT_append aRep (repT_three zRep tRep uRep)
  have hs : (heisBase ()).size = heisT.length := hB.1
  exact slpOK_of hB rfl (by rw [hs]; exact heis_k)

end Certificates
