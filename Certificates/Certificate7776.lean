module

public import CFSG.Milestones.ASVolI.F48.Rest.U52eInputs
import Certificates.Kernel.U52.NormEGlue

public section

namespace Certificates

open CertificateChecks.KernelU52

open CFSG CFSG.ASVolI CFSG.Sporadic.HNOddCore in
theorem certificate7776 :
    (∀ β ∈ arrGen 462 burnsideF48t_u52BArr,
      (∀ k ∈ arrGen 462 (burnsideF48t_u52KArr ()),
        β * k * β⁻¹ ∈ arrGen 462 (burnsideF48t_u52KArr ())) →
      β * β ∈ arrGen 462 (burnsideF48t_u52KArr ()) → β ∉ arrGen 462 (burnsideF48t_u52KArr ()) →
      ∃ k ∈ arrGen 462 (burnsideF48t_u52KArr ()),
        β * k ∈ arrGen 462 (burnsideF48t_u52S0Arr ()) ∧ β * k ≠ 1) ∧
    (∀ β ∈ arrGen 462 burnsideF48t_u52BArr,
      (∀ k ∈ arrGen 462 (burnsideF48t_u52KArr ()),
        (CFSG.ONSchreier.permOfArr 462 (burnsideF48t_u52eLArr ())[4]! * β) * k *
          (CFSG.ONSchreier.permOfArr 462 (burnsideF48t_u52eLArr ())[4]! * β)⁻¹ ∈
          arrGen 462 (burnsideF48t_u52KArr ())) →
      (CFSG.ONSchreier.permOfArr 462 (burnsideF48t_u52eLArr ())[4]! * β) *
          (CFSG.ONSchreier.permOfArr 462 (burnsideF48t_u52eLArr ())[4]! * β) ∈
        arrGen 462 (burnsideF48t_u52KArr ()) →
      ∃ j < 4, CFSG.ONSchreier.permOfArr 462 (burnsideF48t_u52eLArr ())[4]! * β ∈
        arrGen 462 (burnsideF48t_u52eKG j ())) :=
  ⟨fun _ hβ hβK hββ hnot => u52ne_testB hβ hβK hββ hnot,
    fun _ hβ htK htt => u52ne_testF hβ htK htt⟩

end Certificates
