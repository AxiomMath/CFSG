module

import Certificates.Kernel.LocalComp.WittA7042
public import CFSG.Quasithin.Recognition.M22UniqueDataInputs
import Certificates.Kernel.LocalComp.WittA7041

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin MulAction CFSG.ComponentClassification.WittDesign in
open CFSG.Quasithin.Asc94 in
open scoped Pointwise in
theorem certificate7042 :
    (m22Count (fun σ => σ 0 = 0 ∧ ∀ p ∈ m22HexadL, σ p ∈ m22HexadL) = 960)
    ∧ (∀ y : Fin 22, y ∉ m22HexadL →
       0 < m22Count (fun σ => σ 0 = 0 ∧ (∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧ σ 3 = y)) :=
  ⟨KernelLC.Witt.count_ptHex, KernelLC.Witt.count_ptHex_trans⟩

end Certificates
