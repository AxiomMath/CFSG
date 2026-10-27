module

public import Certificates.Data.CFSGNative.Fi22.Certificate
import Certificates.Kernel.Fi22Core.OrbData

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi22.Native

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native in
theorem certificate1005 : fi22Certificate 3 = true := by
  have h := KernelFi22C.fi22_cert
  unfold fi22Certificate
  rw [KernelFi22C.orbitData_eq]
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, ⟨h2, h3⟩, h4⟩

end Certificates
