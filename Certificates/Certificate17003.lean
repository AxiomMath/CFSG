module

public import CFSG.Quasithin.Recognition.M12AscL2

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.OuterData Subgroup Equiv

namespace CertificateChecks.Batch17003

open CFSG CFSG.Quasithin CFSG.Quasithin.OuterData Subgroup Equiv

private theorem card_normD_0 : Nat.card {σ : Perm (Fin 6) // Equiv.Perm.sign σ = 1 ∧ NormDb σ = true} = 36 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

private theorem card_normE_1 : Nat.card {σ : Perm (Fin 6) // Equiv.Perm.sign σ = 1 ∧ NormEb σ = true} = 36 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

end CertificateChecks.Batch17003

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.OuterData Subgroup Equiv in
theorem certificate17003 : (
 Nat.card {σ : Perm (Fin 6) // Equiv.Perm.sign σ = 1 ∧ NormDb σ = true} = 36 
)
    ∧ (
 Nat.card {σ : Perm (Fin 6) // Equiv.Perm.sign σ = 1 ∧ NormEb σ = true} = 36 
) := by
  exact ⟨@CertificateChecks.Batch17003.card_normD_0, @CertificateChecks.Batch17003.card_normE_1⟩

end Certificates
