module

public import CFSG.Milestones.ASVolI.F48.Rest.U52eInputs
import Certificates.Kernel.U52.NormEGlue

public section

namespace Certificates

open CertificateChecks.KernelU52

open CFSG CFSG.ASVolI CFSG.Sporadic.HNOddCore in
theorem certificate7774 : ∀ p ∈ arrGen 462 burnsideF48t_u52P1Arr, ∀ x : Equiv.Perm (Fin 462),
    (x = p ∨ x = CFSG.ONSchreier.permOfArr 462 (burnsideF48t_u52eLArr ())[4]! * p) → x 165 ≠ 165 →
    (∀ j, (j = 0 ∨ j = 1) →
      (∀ k ∈ arrGen 462 (burnsideF48t_u52eKG j ()),
        x * k * x⁻¹ ∈ arrGen 462 (burnsideF48t_u52eKG j ())) →
      x * x ∉ arrGen 462 (burnsideF48t_u52eKG j ())) ∧
    ((∀ k ∈ arrGen 462 (burnsideF48t_u52eKG 2 ()),
        x * k * x⁻¹ ∈ arrGen 462 (burnsideF48t_u52eKG 2 ())) →
      x * x ∈ arrGen 462 (burnsideF48t_u52eKG 2 ()) → ∃ w ∈ burnsideF48t_u52eXW,
        (burnsideF48s_ev (fun l : Fin 5 =>
          CFSG.ONSchreier.permOfArr 462 (burnsideF48t_u52eLArr ())[(l : ℕ)]!) w)⁻¹ * x ∈
          arrGen 462 (burnsideF48t_u52eKG 2 ())) := by
  refine fun p hp x hx hfix => ⟨fun j hj hxH hxx => ?_, fun hxH hxx => ?_⟩
  all_goals
    have hx' : x ∈ CFSG.ASVolI.burnsideF48t_u52P1' ∨ u52neσ 4 * x ∈ CFSG.ASVolI.burnsideF48t_u52P1' := by
      rcases hx with rfl | rfl
      · exact Or.inl hp
      · refine Or.inr ?_
        change u52neσ 4 * (u52neσ 4 * p) ∈ _
        rw [← mul_assoc, u52ne_ff, one_mul]
        exact hp
  · have := (u52ne_test1 x hx' hfix j (by omega) hxH hxx).1
    omega
  · exact (u52ne_test1 x hx' hfix 2 (by norm_num) hxH hxx).2

end Certificates
