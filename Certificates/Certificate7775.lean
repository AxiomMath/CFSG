module

public import CFSG.Milestones.ASVolI.F48.Rest.U52eInputs
import Certificates.Kernel.U52.NormEGlue

public section

namespace Certificates

open CertificateChecks.KernelU52

open CFSG CFSG.ASVolI CFSG.Sporadic.HNOddCore in
theorem certificate7775 : ∀ p ∈ arrGen 462 burnsideF48t_u52P2Arr, ∀ y : Equiv.Perm (Fin 462),
    (y = p ∨ y = CFSG.ONSchreier.permOfArr 462 (burnsideF48t_u52eLArr ())[4]! * p) → y 0 ≠ 0 →
    ((∀ k ∈ arrGen 462 (burnsideF48t_u52eKG 2 ()),
        y * k * y⁻¹ ∈ arrGen 462 (burnsideF48t_u52eKG 2 ())) →
      y * y ∈ arrGen 462 (burnsideF48t_u52eKG 2 ()) → ∃ w ∈ burnsideF48t_u52eYW,
        (burnsideF48s_ev (fun l : Fin 5 =>
          CFSG.ONSchreier.permOfArr 462 (burnsideF48t_u52eLArr ())[(l : ℕ)]!) w)⁻¹ * y ∈
          arrGen 462 (burnsideF48t_u52eKG 2 ())) ∧
    ((∀ k ∈ arrGen 462 (burnsideF48t_u52eKG 3 ()),
        y * k * y⁻¹ ∈ arrGen 462 (burnsideF48t_u52eKG 3 ())) →
      y * y ∉ arrGen 462 (burnsideF48t_u52eKG 3 ())) := by
  refine fun p hp y hy hfix => ⟨fun hyH hyy => ?_, fun hyH hyy => ?_⟩
  all_goals
    have hy' : y ∈ CFSG.ASVolI.burnsideF48t_u52P2' ∨ u52neσ 4 * y ∈ CFSG.ASVolI.burnsideF48t_u52P2' := by
      rcases hy with rfl | rfl
      · exact Or.inl hp
      · refine Or.inr ?_
        change u52neσ 4 * (u52neσ 4 * p) ∈ _
        rw [← mul_assoc, u52ne_ff, one_mul]
        exact hp
  · exact (u52ne_test2 y hy' hfix 2 (Or.inl rfl) hyH hyy).2
  · have := (u52ne_test2 y hy' hfix 3 (Or.inr rfl) hyH hyy).1
    omega

end Certificates
