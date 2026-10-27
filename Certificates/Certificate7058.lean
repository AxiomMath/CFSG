module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23L34DataInputs
import Certificates.Kernel.LocalComp.WittA7058

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelLC.Witt in
open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.ComponentClassification.WittDesign in
open CFSG.Quasithin.Asc94 in
theorem certificate7058 :
    (∀ h ∈ m22Hex01L, h.toFinset ∈ hexadList)
    ∧ (m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧
       ∀ h ∈ m22Hex01L, ∀ p ∈ h, σ p ∈ h) = 16)
    ∧ (m22Count (fun σ => ∀ p ∈ m22HexadL, σ p = p) = 16)
    ∧ (∀ h ∈ m22Hex01Others, m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧
       (∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧ ∀ p ∈ h, σ p ∈ h) = 48) :=
  ⟨hex01_mem, count_kernel_point, count_kernel_hexad, count_two_hexads⟩

end Certificates
