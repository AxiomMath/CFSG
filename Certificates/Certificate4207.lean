module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvGenPFam
import Certificates.Kernel.J4Ov.G4207
public import Certificates.Certificate3084

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Ov in
theorem certificate4207 : ∀ i < 49, (repData.getD i ⟨0, "", true, 0⟩).exc = false →
    (∃ s ∈ P0 ⊔ (Eg uJ 11).map
        (MulAut.conj (zEl (repData.getD i ⟨0, "", true, 0⟩))⁻¹).toMonoidHom,
      s ∈ Hj ∧ s ∉ Eg uJ 11 ∧ ∃ p, (p = 11 ∨ p = 23) ∧ s ^ p ∈ Eg uJ 11) ∧
    ∃ j < 11, (zEl (repData.getD i ⟨0, "", true, 0⟩))⁻¹ * uJ j *
      zEl (repData.getD i ⟨0, "", true, 0⟩) ∉ Hj :=
  fun _ hi hexc => KernelJ4Ov.genP4207 Certificates.certificate3084 hi hexc

end Certificates
