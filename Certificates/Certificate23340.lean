module

import Certificates.Kernel.Misc.Perm.K23340
import CFSG.Certificates.Kernel.Misc.Perm23340Sound
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.NormNum.GCD

public section

namespace Certificates

open CertificateChecks

theorem certificate23340 : ∀ σ u : Equiv.Perm (Fin 6), σ * σ = 1 → Equiv.Perm.sign u = 1 → u ≠ 1 →
    u * σ = σ * u → u ^ 45 = 1 → ∃ c : Equiv.Perm (Fin 6), Equiv.Perm.sign c = 1 ∧
      c * σ = σ * c ∧ (u⁻¹ * c * u * c⁻¹) ^ 45 ≠ 1 :=
  CFSG.KC.Misc.C23340.chk23340_sound KernelMisc.K23340.chk_true

end Certificates
