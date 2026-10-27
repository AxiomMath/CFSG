module

public import CFSG.Milestones.ASVolI.F48.D43.EDefs
public import CFSG.Milestones.ASVolI.F48.D43.EInputs
import Certificates.Kernel.D43.EBase
import CFSG.Milestones.ASVolI.F48.D43.Chain

public section

open CFSG.ASVolI CertificateChecks.KernelD43

namespace Certificates

open CFSG CFSG.ASVolI in
theorem certificate7810 : burnsideF48d_frob ^ 3 = 1 ∧ burnsideF48d_frob ≠ 1 ∧
    (∀ p ∈ burnsideF48d_aptF, burnsideF48d_frob p = p) ∧
    (∀ p ∈ burnsideF48d_line, burnsideF48d_frob p ∈ burnsideF48d_line) ∧
    burnsideF48d_frob * burnsideF48d_σ 0 = burnsideF48d_σ 0 * burnsideF48d_frob ∧
    burnsideF48d_frob * burnsideF48d_σ 1 = burnsideF48d_σ 1 * burnsideF48d_frob ∧
    (burnsideF48d_σ 0 * burnsideF48d_σ 1) ^ 6 = 1 ∧
    (∀ k < 15, burnsideF48d_frob⁻¹ * (burnsideF48d_σ (k + 2) * burnsideF48d_frob) =
      burnsideF48s_ev (fun j : Fin 18 => burnsideF48dE_σ j) (burnsideF48dE_PhiW.getD k [])) ∧
    ∀ r ∈ burnsideF48d_R13 ++ burnsideF48d_R23,
      burnsideF48s_ev (fun j : Fin 18 => burnsideF48dE_σ j) r = 1 :=
  e_facts burnsideF48d_ωF burnsideF48d_card_F burnsideF48d_ωF_spec
    (fun k => (burnsideF48d_g burnsideF48d_σF burnsideF48d_ωF k).val)
    (fun k => burnsideF48d_g_val burnsideF48d_σF burnsideF48d_ωF burnsideF48d_σF_apply
      burnsideF48d_ωF_spec k)
    burnsideF48d_base

end Certificates
