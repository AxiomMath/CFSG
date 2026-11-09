module

public import Certificates.Data.HatA7Loc
import CFSG.Certificates.Kernel.PermCent.FastDecide

public section

namespace CertificateChecks.Batch7251

open Equiv HatA7Loc

open scoped CFSG.Certificates.Kernel.PkCV.FastDecide

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem cent1_ok : cent1 := by
  unfold cent1
  decide +kernel

theorem cent2_aux : ∀ σ : Perm (Fin 7), σ * c = c * σ → σ ^ 16 = 1 → Perm.sign σ = 1 →
    σ = 1 ∨ σ = t0 ∨ σ = v2 ∨ σ = v3 := by
  decide +kernel

theorem cent2_ok : cent2 := by
  unfold cent2
  intro σ h1 h2 h3
  exact cent2_aux σ h2 h3 h1

theorem cent3_aux : ∀ σ : Perm (Fin 7), σ * d = d * σ → σ ^ 16 = 1 → Perm.sign σ = 1 →
    σ = 1 := by
  decide +kernel

theorem cent3_ok : cent3 := by
  unfold cent3
  intro σ h1 h2 h3
  exact cent3_aux σ h2 h3 h1

end CertificateChecks.Batch7251

namespace Certificates

theorem certificate7251 : HatA7Loc.check = true :=
  decide_eq_true (p := HatA7Loc.stmt)
    (⟨CertificateChecks.Batch7251.cent1_ok, CertificateChecks.Batch7251.cent2_ok,
      CertificateChecks.Batch7251.cent3_ok⟩ : HatA7Loc.cent1 ∧ HatA7Loc.cent2 ∧ HatA7Loc.cent3)

end Certificates
