module

public import CFSG.Quasithin.H13.U3SixUniqueInputs

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.U3 Matrix

namespace CertificateChecks.Batch17006

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.U3 Matrix

private theorem kWords_fix_0 : ∀ b ∈ [1, 18], ∀ k ∈ kWords b, wordApply k 15 = 15 ∧ wordApply k b = b := by
  decide +kernel

private theorem kWords_fixed_only_1 : ∀ b ∈ [1, 18], ∀ c < 64, (kWords b).all (fun k => wordApply k c == c) →
    c = 0 ∨ c = 15 ∨ c = b ∨ c = 15 ^^^ b := by
  decide +kernel

private theorem deriveSteps_ok_2 : deriveCheck [1, 2, 4, 8, 16, 32] deriveSteps = true := by
  decide +kernel

private theorem deriveSteps_cover_3 : ∀ c < 64, c = 0 ∨ c ∈ [1, 2, 4, 8, 16, 32] ∨
    c ∈ deriveSteps.map Prod.fst := by
  decide +kernel

end CertificateChecks.Batch17006

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.U3 Matrix in
theorem certificate17006 : (
 ∀ b ∈ [1, 18], ∀ k ∈ kWords b, wordApply k 15 = 15 ∧ wordApply k b = b 
)
    ∧ (
 ∀ b ∈ [1, 18], ∀ c < 64, (kWords b).all (fun k => wordApply k c == c) →
    c = 0 ∨ c = 15 ∨ c = b ∨ c = 15 ^^^ b 
)
    ∧ (
 deriveCheck [1, 2, 4, 8, 16, 32] deriveSteps = true 
)
    ∧ (
 ∀ c < 64, c = 0 ∨ c ∈ [1, 2, 4, 8, 16, 32] ∨
    c ∈ deriveSteps.map Prod.fst 
) := by
  exact ⟨@CertificateChecks.Batch17006.kWords_fix_0, @CertificateChecks.Batch17006.kWords_fixed_only_1, @CertificateChecks.Batch17006.deriveSteps_ok_2, @CertificateChecks.Batch17006.deriveSteps_cover_3⟩

end Certificates
