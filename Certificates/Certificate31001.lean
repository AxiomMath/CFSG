module

public import CFSG.RankThree.Native.HSMcLSmallData
import Certificates.Kernel.CentGenK.Glue
import Certificates.Kernel.CentGenK.HS
import Certificates.Kernel.HS100.Chain
import CFSG.RankThree.Native.HSMcLSmall

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.CentGenK CFSG.KS.Raw.Orb CFSG.RankThree.Native CertificateChecks.KernelHS100 in
open CFSG.RankThree.Native in
theorem certificate31001 : ∃ e f s₁ s₂ : Equiv.Perm (Fin 100),
    Subgroup.closure {s₁, s₂} = hs100P ∧ e ∈ hs100P ∧ f ∈ hs100P ∧
    e ^ 5 = 1 ∧ f ^ 5 = 1 ∧ e * f = f * e ∧ e ≠ 1 ∧ (∀ k < 5, f ≠ e ^ k) ∧
    s₁ * e = e * s₁ ∧ s₂ * f = f * s₂ := by
  have hA : PRep 100 7 (HP.F 0) hs100A :=
    prep_of_rep (by rw [← hs100Arr_eq 0 (by norm_num)]; exact rep_hs100A)
  have hB : PRep 100 7 (HP.F 1) hs100B :=
    prep_of_rep (by rw [← hs100Arr_eq 1 (by norm_num)]; exact rep_hs100B)
  exact cg_facts hA hB KernelCentGenK.HS.hs_ok

end Certificates
