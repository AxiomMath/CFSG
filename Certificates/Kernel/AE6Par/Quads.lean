module

public import Certificates.Data.Kernel.AE6Par.Defs

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelAE6Par

open Equiv CFSG.ClassicalInvolution.Q3 Certificates.AE6Par Certificates.AE6Par.K

theorem ae6par_quads : ∀ a b : Fin 8, a < b → ∀ c : Fin 8, b < c → ∀ d : Fin 8, c < d →
    quadB a b c d = true := by
  decide +kernel

theorem ae6par_masksP : AE.affinePlanes.map maskF = affM ∧ planes2.map maskF = p2M := by
  decide +kernel

theorem ae6par_masksT : tab1.map (fun e => maskF (d0.map (swapsPerm e).toEmbedding)) = tab1M ∧
    tab2.map (fun e => maskF (b0.map (swapsPerm e).toEmbedding)) = tab2M ∧
    ∀ e ∈ tab2, d0.map (swapsPerm e).toEmbedding = d0 := by
  decide +kernel

end CertificateChecks.KernelAE6Par
