module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213HatHGroups
import Certificates.Kernel.HatHe.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.H13.Ch4 in
theorem certificate7167 : Nat.card HatH.heP0 = 2 ^ 9 ∧
    (∀ A : Subgroup (Equiv.Perm (Fin 8330)), A ≤ HatH.heP0 →
      A ≤ HatH.heP0.map (MulAut.conj HatH.heD0).toMonoidHom →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A ≤ 63) ∧
    Nat.card HatH.heP1 = 2 ^ 10 ∧
    (∀ A : Subgroup (Equiv.Perm (Fin 8330)), A ≤ HatH.heP1 →
      A ≤ HatH.heP1.map (MulAut.conj HatH.heD1).toMonoidHom →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A ≤ 63) :=
  ⟨KernelHatHe.facts0.1, KernelHatHe.facts0.2, KernelHatHe.facts1.1, KernelHatHe.facts1.2⟩

end Certificates
