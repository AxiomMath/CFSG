module

import Certificates.Kernel.U52.NormGlue
public import CFSG.Milestones.ASVolI.F48.Rest.U52Inputs

public section

namespace Certificates

open CertificateChecks.KernelU52

open CFSG CFSG.ASVolI CFSG.Sporadic.HNOddCore in
theorem certificate7770 :
    (∀ c ∈ arrGen 462 (burnsideF48t_u52KArr ()), ∃ m < 9, c =
      burnsideF48s_ev (fun l : Fin 4 => CFSG.ONSchreier.permOfArr 462 burnsideF48t_u52LArr[(l : ℕ)]!)
        (burnsideF48t_u52KW.getD m [])) ∧
    (∀ m < 9,
      burnsideF48s_ev (fun l : Fin 4 => CFSG.ONSchreier.permOfArr 462 burnsideF48t_u52LArr[(l : ℕ)]!)
        (burnsideF48t_u52KW.getD m []) ∈ arrGen 462 (burnsideF48t_u52KArr ())) ∧
    (∀ x ∈ arrGen 462 burnsideF48t_u52P1Arr, x ∉ arrGen 462 burnsideF48t_u52P2Arr →
      (∀ k ∈ arrGen 462 (burnsideF48t_u52KArr ()),
        x * k * x⁻¹ ∈ arrGen 462 (burnsideF48t_u52KArr ())) →
      x * x ∈ arrGen 462 (burnsideF48t_u52KArr ()) → ∃ w ∈ burnsideF48t_u52XW,
        (burnsideF48s_ev (fun l : Fin 4 =>
          CFSG.ONSchreier.permOfArr 462 burnsideF48t_u52LArr[(l : ℕ)]!) w)⁻¹ * x ∈
          arrGen 462 (burnsideF48t_u52KArr ())) ∧
    (∀ y ∈ arrGen 462 burnsideF48t_u52P2Arr, y ∉ arrGen 462 burnsideF48t_u52P1Arr →
      (∀ k ∈ arrGen 462 (burnsideF48t_u52KArr ()),
        y * k * y⁻¹ ∈ arrGen 462 (burnsideF48t_u52KArr ())) →
      y * y ∈ arrGen 462 (burnsideF48t_u52KArr ()) → ∃ w ∈ burnsideF48t_u52YW,
        (burnsideF48s_ev (fun l : Fin 4 =>
          CFSG.ONSchreier.permOfArr 462 burnsideF48t_u52LArr[(l : ℕ)]!) w)⁻¹ * y ∈
          arrGen 462 (burnsideF48t_u52KArr ())) :=
  ⟨u52n_K_sub, fun _ hm => u52n_κ_mem hm, fun _ hx hx2 hxK hxx => u52n_xred hx hx2 hxK hxx,
    fun _ hy hy1 hyK hyy => u52n_yred hy hy1 hyK hyy⟩

end Certificates
