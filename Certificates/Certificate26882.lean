module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08HCheck
import Certificates.Kernel.EvenSporM22.HS08Checks
import Certificates.Kernel.EvenSporM22.HS08DChecks
import Certificates.Kernel.EvenSporM22.HS08NChecks
import CFSG.Certificates.Kernel.EvenSporM22.HS08JSound
import CFSG.Certificates.Kernel.EvenSporM22.HS08NSound

public section

open CFSG.EvenSporadicStandard.M22Std.HS08Check CFSG.EvenSporadicStandard.M22Std.OutCheck
  CFSG.EvenSporadicStandard.M22Std.E32Check CFSG.KC.EvenSporM22

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M22Std.HS08Check in
theorem certificate26882 : normCheck = true := by
  have hs := Certificates.certificate24800
  simp only [s0Check, Bool.and_eq_true, decide_eq_true_eq] at hs
  have hj := jTabs_eq_jLit KernelEvenSporM22.jOK_jLit
  have hl := KernelEvenSporM22.hs08dLens
  have h : NormPropJ jTabs := by
    rw [hj]
    exact hs08normPropJ hs.1.1.1.1.1.1 hl.1 KernelEvenSporM22.hs08dGens_valid
      KernelEvenSporM22.hs08dReps_valid KernelEvenSporM22.hs08nLens KernelEvenSporM22.hs08nCent
      KernelEvenSporM22.hs08nW4 KernelEvenSporM22.hs08nW6 KernelEvenSporM22.hs08nW10
      KernelEvenSporM22.hs08nMem KernelEvenSporM22.hs08nOrbs KernelEvenSporM22.hs08nNorms
      KernelEvenSporM22.hs08nInv
  have h' : NormProp := h
  exact decide_eq_true h'

end Certificates
