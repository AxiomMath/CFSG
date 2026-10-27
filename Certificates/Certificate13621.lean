module

import Certificates.Kernel.Fi22Reps.Final
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22WitnessBase

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi22 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three in
theorem certificate13621 : 
    (∀ v : Fin 3510, xRep 0 • v ≠ v) ∧
    (∃ t : J, orderOf t = 4 ∧ t * xRep 0 = xRep 0 * t) ∧
    Nat.card (Subgroup.centralizer ({xRep 0} : Set J)) ≤ 34992 ∧
    (∀ k ∈ [1, 2, 3], Nat.card {g : J // g ∈ Subgroup.centralizer ({xRep k} : Set J) ∧
      ∀ v : Fin 3510, xRep k • v = v → g • v = v} ≤ 3) ∧
    ∀ k ∈ [1, 2, 3], ∀ d ∈ D, d * xRep k = xRep k * d → ∀ d' ∈ D, d' * xRep k = xRep k * d' →
      d ≠ d' → d * d' = d' * d →
        ∃ e ∈ D, e * xRep k = xRep k * e ∧ e * d' = d' * e ∧ e * d ≠ d * e :=
  ⟨KernelFi22Reps.xRep_zero_smul_ne, KernelFi22Reps.exists_orderOf_four_comm,
    KernelFi22Reps.card_centralizer_xRep_zero_le,
    fun _ hk => KernelFi22Reps.card_centralizer_fix_le hk, fun _ hk => KernelFi22Reps.sep_xRep hk⟩

end Certificates
