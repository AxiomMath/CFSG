module

public import CFSG.Sporadic.Schreier.RuDefs
import Certificates.Kernel.CentGenK.Glue
import Certificates.Kernel.CentGenK.Ru
import Certificates.Kernel.SporSch.Ru.Gens
import CFSG.Sporadic.Schreier.RuReps

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.CentGenK CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Sporadic.RuSchreier
  CertificateChecks.KernelSporSch in
open CFSG.Sporadic.RuSchreier in
theorem certificate31002 : ∃ e f s₁ s₂ : Equiv.Perm (Fin 4060),
    Subgroup.closure {s₁, s₂} = ruP ∧ e ∈ ruP ∧ f ∈ ruP ∧
    e ^ 5 = 1 ∧ f ^ 5 = 1 ∧ e * f = f * e ∧ e ≠ 1 ∧ (∀ k < 5, f ≠ e ^ k) ∧
    s₁ * e = e * s₁ ∧ s₂ * f = f * s₂ := by
  have e0 : ruA0A = unpack 4060 12 (RuT4060.L 0) := RuG.a0_eq
  have e1 : ruA1A = unpack 4060 12 (RuT4060.L 1) := RuG.a1_eq
  have hA : PRep 4060 12 (RuT4060.L 0) ruA0 := prep_of_rep (by rw [← e0]; exact rep_ruA0)
  have hB : PRep 4060 12 (RuT4060.L 1) ruA1 := prep_of_rep (by rw [← e1]; exact rep_ruA1)
  exact cg_facts hA hB KernelCentGenK.Ru.ru_ok

end Certificates
