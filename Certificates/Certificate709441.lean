
module

public import CFSG.ClassicalInvolution.Phan.PhanDn.CompGraph
public import CFSG.Monster.B.Recog.GenericWalkHomotopy
import Certificates.Kernel.D4Q2K.Glue
import CFSG.ClassicalInvolution.Phan.PhanDn.D4Q2.CoverBase
import CFSG.Certificates.Kernel.RankElimSound
import CFSG.Sporadic.Co1Patterson.TriangulableByBridge
import CFSG.Monster.B.GSide.HomotopyLocal

public section

namespace Certificates

open CertificateChecks

open CFSG.ClassicalInvolution.PhanDn.D4Q2

open CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.PhanDn in
theorem certificate709441 : ∀ {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K},
    IsUnitaryInvolution σ → Nat.card K = 4 →
      (compGraph σ).Connected ∧ CFSG.Monster.B.Recog.Triangulable (compGraph σ) := by
  refine fun {K} _ _ _ {σ} hσ hK => ?_
  obtain ⟨ω, hω, hσω⟩ := exists_omega hσ hK
  obtain ⟨e⟩ := nonempty_nbrGraph_iso hσ hK hω hσω KernelD4Q2K.checks
  have hok := KernelD4Q2K.elim
  have hconn := SimpleGraph.Connected.mk (CFSG.KC.RankElim.preconnected_of_ok hok)
  have htri := CFSG.Sporadic.Co1Patterson.TriangulableBy.triangulable
    (CFSG.KC.RankElim.triangulableBy_of_ok (T := fun _ => True) (fun _ _ _ _ => trivial) hok)
  exact ⟨(SimpleGraph.Iso.connected_iff e).mp hconn,
    (CFSG.Monster.B.GSide.triangulable_iff_of_iso e).mp htri⟩

end Certificates
