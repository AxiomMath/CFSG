module

public import CFSG.Milestones.ASVolI.F48.Rest.U52eInputs2
import Certificates.Kernel.U52.GlueX
import Certificates.Kernel.U52.BindF
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LieType.BorelTits.CompleteFlag

set_option maxRecDepth 400000

namespace CertificateChecks.Batch7778

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.WordF CFSG.KC.Misc.ArrEnum
  CertificateChecks.KernelU52 CertificateChecks.KernelU52G CertificateChecks.KernelU52F

theorem rL5 : ∀ i < 5, Rng 462 9 (LFP i) ∧ Rng 462 9 (LFPI i) := fun i hi =>
  ⟨fun x hx => (lf_range i hi x hx).1, fun x hx => (lf_range i hi x hx).2⟩

theorem rE5 (wd : List (Fin 5 × Bool)) :
    Rng 462 9 (evFK 462 9 (mask 9) (pidn 462 9) LFP LFPI wd) :=
  rng_evFK (by norm_num) (by norm_num) (by norm_num) rL5 wd

theorem cE5 (wd : List (Fin 5 × Bool)) :
    Canon 462 9 (evFK 462 9 (mask 9) (pidn 462 9) LFP LFPI wd) :=
  canon_evFK (by norm_num) (by norm_num) (by norm_num) LFP LFPI wd

local macro "u52ed" : tactic => `(tactic|
  ((repeat' (first
    | exact rE _
    | exact cE _
    | exact rE5 _
    | exact cE5 _
    | exact cPC _ _
    | exact cId
    | exact rId
    | exact fun _ => cE _
    | exact fun _ => cE5 _
    | exact fun _ => rE _
    | exact fun _ => rE5 _
    | apply rPC
    | apply rng_getD
    | apply canon_getD)) <;> done))

theorem klOK : burnsideF48t_u52eKLOK () = true := by
  unfold burnsideF48t_u52eKLOK
  simp (disch := u52ed) only [burnsideF48t_u52KL, burnsideF48t_u52eKL, ev_eq, evF_eq, pidE,
    getD_map_unpack, pcE, peqE, List.all_map, Function.comp_def, allBelowN_eq_allN]
  decide +kernel

end CertificateChecks.Batch7778

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ASVolI in
theorem certificate7778 : burnsideF48t_u52eKLOK () = true :=
  CertificateChecks.Batch7778.klOK

end Certificates

end
