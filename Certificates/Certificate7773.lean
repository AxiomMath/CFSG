module

public import CFSG.Milestones.ASVolI.F48.Rest.U52eInputs
import Certificates.Kernel.U52.GlueX
import Certificates.Kernel.U52.BindF
import CFSG.Certificates.Kernel.Misc.ArrBind
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LieType.BorelTits.CompleteFlag

set_option maxRecDepth 400000

namespace CertificateChecks.Batch7773

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.WordF CFSG.KC.Misc.ArrEnum
  CertificateChecks.KernelU52 CertificateChecks.KernelU52G CertificateChecks.KernelU52F

private theorem rL5 : ∀ i < 5, Rng 462 9 (LFP i) ∧ Rng 462 9 (LFPI i) := fun i hi =>
  ⟨fun x hx => (lf_range i hi x hx).1, fun x hx => (lf_range i hi x hx).2⟩

private theorem rE5 (wd : List (Fin 5 × Bool)) :
    Rng 462 9 (evFK 462 9 (mask 9) (pidn 462 9) LFP LFPI wd) :=
  rng_evFK (by norm_num) (by norm_num) (by norm_num) rL5 wd

private theorem cE5 (wd : List (Fin 5 × Bool)) :
    Canon 462 9 (evFK 462 9 (mask 9) (pidn 462 9) LFP LFPI wd) :=
  canon_evFK (by norm_num) (by norm_num) (by norm_num) LFP LFPI wd

private theorem fBind : arrBind burnsideF48t_u52eF 462 9 (LFP 4) = true := by
  quickRfl

private theorem fPerm : permOK 462 9 (mask 9) (462 * 9) (LFP 4) (LFP 4) = true := by
  quickRfl

private theorem rF : Rng 462 9 (LFP 4) := rng_of_permOK fPerm

private theorem cF : Canon 462 9 (LFP 4) := canon_of_permOK fPerm

local macro "u52ed" : tactic => `(tactic|
  ((repeat' (first
    | exact rE _
    | exact cE _
    | exact rE5 _
    | exact cE5 _
    | exact cPC _ _
    | exact cId
    | exact rId
    | exact rF
    | exact cF
    | exact fun _ => cE _
    | exact fun _ => cE5 _
    | exact fun _ => rE _
    | exact fun _ => rE5 _
    | exact rS _ (by decide)
    | exact cS _ (by decide)
    | apply rPC
    | apply rng_getD
    | apply canon_getD)) <;> done))

private theorem invOK : burnsideF48t_u52eInvOK () = true := by
  have hs : (burnsideF48t_u52eLArr ()).size = 5 := by decide +kernel
  have hsi : (burnsideF48t_u52eLInv ()).size = 5 := by
    simp only [burnsideF48t_u52eLInv, Array.size_map, hs]
  unfold burnsideF48t_u52eInvOK
  simp only [hs, hsi, beq_self_eq_true, Bool.true_and]
  refine CFSG.ONSchreier.allBelowN_iff.2 fun i hi => ?_
  rw [lf_eq i hi, lfi_eq i hi]
  exact pisInv_unpack (allN_spec lfPerm i hi)

private theorem fOK : burnsideF48t_u52eFOK () = true := by
  have hF : burnsideF48t_u52eF = unpack 462 9 (LFP 4) := arrBind_sound fBind
  unfold burnsideF48t_u52eFOK
  simp (disch := u52ed) only [hF, gens_eq, pisInv_unpack fPerm, getElem!_unpack, pcE, siftX_eq,
    List.all_toArray, List.all_cons, List.all_nil, Bool.true_and, Bool.and_true]
  decide +kernel

private theorem relOK : burnsideF48t_u52eRelOK () = true := by
  unfold burnsideF48t_u52eRelOK
  simp (disch := u52ed) only [evF_eq, pidE, peqE]
  decide +kernel

private theorem khOK : burnsideF48t_u52eKhOK () = true := by
  unfold burnsideF48t_u52eKhOK
  simp (disch := u52ed) only [burnsideF48t_u52KL, burnsideF48t_u52eKL, burnsideF48t_u52eKG,
    burnsideF48t_closedL, ev_eq, evF_eq, pidE, getD_map_unpack, containsE, pcE, peqE,
    List.length_map, List.all_map, List.all_toArray, List.all_cons, List.all_nil,
    Function.comp_def, allBelowN_eq_allN, Bool.and_true]
  decide +kernel

private theorem candOK : burnsideF48t_u52eCandOK () = true := by
  unfold burnsideF48t_u52eCandOK
  simp (disch := u52ed) only [evF_eq, pidE, pcE, peqE, allBelowN_eq_allN]
  decide +kernel

end CertificateChecks.Batch7773

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ASVolI in
theorem certificate7773 : burnsideF48t_u52eInvOK () = true ∧
    burnsideF48t_u52eFOK () = true ∧
    burnsideF48t_u52eRelOK () = true ∧
    burnsideF48t_u52eKhOK () = true ∧
    burnsideF48t_u52eCandOK () = true :=
  ⟨CertificateChecks.Batch7773.invOK, CertificateChecks.Batch7773.fOK, CertificateChecks.Batch7773.relOK, CertificateChecks.Batch7773.khOK, CertificateChecks.Batch7773.candOK⟩

end Certificates

end
