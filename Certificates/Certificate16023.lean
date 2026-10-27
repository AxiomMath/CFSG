module

public import CFSG.Monster.B.Fischer.InducedChecksInputs

public section

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Fischer CFSG.Monster.Code
  CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu

namespace CertificateChecks.Batch16023

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Fischer CFSG.Monster.Code
  CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu

private theorem genBinv_spec_0 :
    ∀ t : Fin 22, ((psiHom (m22gB⁻¹ : Equiv.Perm (Fin 22)) (coordAt t : Fin 24)) : ℕ) =
      genBinv t + 2 := by
  decide +kernel

private theorem blockWord_letters_1 : ∀ i < 77, ∀ z ∈ blockWord i, z = 1 ∨ z = 2 := by
  decide +kernel

end CertificateChecks.Batch16023

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Fischer CFSG.Monster.Code
  CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu in
theorem certificate16023 : (
    ∀ t : Fin 22, ((psiHom (m22gB⁻¹ : Equiv.Perm (Fin 22)) (coordAt t : Fin 24)) : ℕ) =
      genBinv t + 2
  ) ∧ (
    ∀ i < 77, ∀ z ∈ blockWord i, z = 1 ∨ z = 2
  ) := by
  exact ⟨CertificateChecks.Batch16023.genBinv_spec_0, CertificateChecks.Batch16023.blockWord_letters_1⟩

end Certificates
