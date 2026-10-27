module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.P12Check
import CFSG.Certificates.Kernel.EvenSporP12.Sound
import Certificates.Kernel.EvenSporP12.Checks

public section

open CFSG.EvenSporadicStandard.M12Std.SolomonK.P12

namespace CertificateChecks.Batch450015

open CFSG.EvenSporadicStandard.M12Std.SolomonK.P12

theorem p12_check_12 : p12Check 12 () = true := by
  have h := KernelEvenSporP12.ents12
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [CFSG.KC.EvenSporP12.p12Check_eq (by decide) h1 h2 h3]
  exact KernelEvenSporP12.p12K_12

end CertificateChecks.Batch450015

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M12Std.SolomonK.P12 in
theorem certificate450015 : p12Check 12 () = true :=
  CertificateChecks.Batch450015.p12_check_12

end Certificates
