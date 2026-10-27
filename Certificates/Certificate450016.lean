module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.P12Check
import CFSG.Certificates.Kernel.EvenSporP12.Sound
import Certificates.Kernel.EvenSporP12.Checks

public section

open CFSG.EvenSporadicStandard.M12Std.SolomonK.P12

namespace CertificateChecks.Batch450016

open CFSG.EvenSporadicStandard.M12Std.SolomonK.P12

theorem p12_check_13 : p12Check 13 () = true := by
  have h := KernelEvenSporP12.ents13
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [CFSG.KC.EvenSporP12.p12Check_eq (by decide) h1 h2 h3]
  exact KernelEvenSporP12.p12K_13

end CertificateChecks.Batch450016

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M12Std.SolomonK.P12 in
theorem certificate450016 : p12Check 13 () = true :=
  CertificateChecks.Batch450016.p12_check_13

end Certificates
