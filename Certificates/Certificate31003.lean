module

public import CFSG.Sporadic.HeldB.CertPChainData
public import CFSG.Monster.B.Co2.PermArr
import Certificates.Kernel.CentGenK.Glue
import Certificates.Kernel.CentGenK.He
import Certificates.Kernel.He2111.Final
import CFSG.Sporadic.HeldB.CertPChain

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.HeldB CFSG.Monster.B.Co2 in
private theorem prep_heGen {k : Nat} (hk : k < 2) :
    CFSG.KS.Raw.Orb.PRep 8330 14 (CFSG.KD.He2111.GnT.F k) (permOfArr 8330 (heGen k)) := fun x => by
  have h1 := rep_heGen hk x
  rw [CFSG.KD.He2111.gen_get hk x.2, CFSG.KC.He2111.e14] at h1
  have e : heGenPerm k = permOfArr 8330 (heGen k) := rfl
  rw [CFSG.KD.He2111.mask14, ← e]
  exact h1

open CFSG.KC.CentGenK in
open CFSG.Sporadic.HeldB CFSG.Monster.B.Co2 in
theorem certificate31003 : ∃ e f s₁ s₂ : Equiv.Perm (Fin 8330),
    Subgroup.closure {s₁, s₂} =
        Subgroup.closure {CFSG.Monster.B.Co2.permOfArr 8330 (heGen 0), CFSG.Monster.B.Co2.permOfArr 8330 (heGen 1)} ∧
      e ∈ Subgroup.closure {CFSG.Monster.B.Co2.permOfArr 8330 (heGen 0), CFSG.Monster.B.Co2.permOfArr 8330 (heGen 1)} ∧
      f ∈ Subgroup.closure {CFSG.Monster.B.Co2.permOfArr 8330 (heGen 0), CFSG.Monster.B.Co2.permOfArr 8330 (heGen 1)} ∧
      e ^ 7 = 1 ∧ f ^ 7 = 1 ∧ e * f = f * e ∧ e ≠ 1 ∧ (∀ k < 7, f ≠ e ^ k) ∧
      s₁ * e = e * s₁ ∧ s₂ * f = f * s₂ :=
  cg_facts (prep_heGen (k := 0) (by norm_num)) (prep_heGen (k := 1) (by norm_num))
    KernelCentGenK.He.he_ok

end Certificates
