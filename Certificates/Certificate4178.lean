module

public import Certificates.Kernel.J4Loc.StabAsm

public section

namespace Certificates

open CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc in
theorem certificate4178 : ∀ a ∈ V0F, ∀ b ∈ V0F, ∀ c ∈ V0F, a ≠ 0 → b ≠ 0 → b ≠ a → c ≠ 0 → c ≠ a → c ≠ b →
    c ≠ a ^^^ b → ∃ w : List ℤ, (∀ ℓ ∈ w, ℓ ∈ letters) ∧
      w.foldr act 422 = a ∧ w.foldr act 553 = b ∧ w.foldr act 1131 = c :=
  CertificateChecks.KernelJ4Loc.k4178_basis

end Certificates
