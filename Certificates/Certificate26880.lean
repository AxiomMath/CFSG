module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08HCheck
import Certificates.Kernel.EvenSporM22.HS08Checks
import Certificates.Kernel.EvenSporM22.HS08DChecks
import CFSG.Certificates.Kernel.EvenSporM22.HS08JSound
import CFSG.Certificates.Kernel.EvenSporM22.HS08DSound

public section

open CFSG.EvenSporadicStandard.M22Std.HS08Check CFSG.EvenSporadicStandard.M22Std.OutCheck
  CFSG.KC.EvenSporM22

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M22Std.HS08Check in
theorem certificate26880 : dCheck = true := by
  have hs := Certificates.certificate24800
  simp only [s0Check, Bool.and_eq_true, decide_eq_true_eq] at hs
  have hj := jTabs_eq_jLit KernelEvenSporM22.jOK_jLit
  have hl := KernelEvenSporM22.hs08dLens
  have h : DProp := by
    refine ⟨hl.2.2, CFSG.Decide.nodup_of_bitsetNodup hs08DKey KernelEvenSporM22.hs08dKeys_ok,
      KernelEvenSporM22.hs08dId,
      hs08dTabs_closed hs.1.1.1.1.1.2.2 hs.1.1.1.1.1.1 KernelEvenSporM22.hs08dGens_valid
        KernelEvenSporM22.hs08dReps_valid ⟨hl.1, hl.2.1⟩ KernelEvenSporM22.hs08dRecs_ok, ?_⟩
    rw [hj]
    exact KernelEvenSporM22.hs08dNorm_jLit
  exact decide_eq_true h

end Certificates
