module

public import CFSG.LocalAnalysis.EvenSmallLie.FFourTwo.NativeInputs
import Certificates.Kernel.LocalComp.F42.Gen
import Certificates.Kernel.LocalComp.F42.Big

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.FFourTwo in
theorem certificate3087 : (smallCheck = true)
    ∧ (witCheck = true)
    ∧ (genCheck = true)
    ∧ (cenCheck = true)
    ∧ (chainsCheck = true)
    ∧ ((∀ c < 8, (Pc.preSq cmF 25 22).toList.countP (fun p => CFSG.EvenSmallLie.FFourTwo.mulU p p == c * 2 ^ 22) =
        sqCounts.getD c 0) ∧
      ∃ d : ℕ → ℕ, ∀ p ∈ invCosets (Pc.preSq cmF 25 22), p ∈ compReps ∨
        ∃ m ∈ rMoves, mvOK m p = true ∧ CFSG.EvenSmallLie.FFourTwo.mv m p % 2 ^ 22 ≠ 0 ∧ d (CFSG.EvenSmallLie.FFourTwo.mv m p % 2 ^ 22) + 1 = d p) :=
  ⟨KernelLC.F42.small_ok, KernelLC.F42.wit_ok, KernelLC.F42.gen_okAll, KernelLC.F42.cen_ok,
    KernelLC.F42.chains_ok, KernelLC.F42.sq_ok, KernelLC.F42.bfs_ok⟩

end Certificates
