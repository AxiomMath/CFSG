module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.CentGenK.Glue
import Certificates.Kernel.CentGenK.M12

public section

namespace Certificates

open CFSG.KC.CentGenK CFSG.KS.Raw.Orb CertificateChecks.KernelCentGenK.M12 in
open CFSG.Blueprint in
theorem certificate31011 : ∃ e f s₁ s₂ : Equiv.Perm (Fin 12),
    Subgroup.closure {s₁, s₂} = NativeSporadic.M12 ∧ e ∈ NativeSporadic.M12 ∧
      f ∈ NativeSporadic.M12 ∧
      e ^ 3 = 1 ∧ f ^ 3 = 1 ∧ e * f = f * e ∧ e ≠ 1 ∧ (∀ k < 3, f ≠ e ^ k) ∧
      s₁ * e = e * s₁ ∧ s₂ * f = f * s₂ := by
  have hA : PRep 12 4 A0 (List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] *
      List.formPerm [5, 11]) := by
    unfold PRep
    decide +kernel
  have hB : PRep 12 4 A1 (List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] *
      List.formPerm [4, 11, 10] * List.formPerm [5, 9, 6]) := by
    unfold PRep
    decide +kernel
  exact cg_facts hA hB m12_ok

end Certificates
