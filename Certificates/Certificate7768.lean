module

public import CFSG.Milestones.ASVolI.F48.Rest.U52Inputs
import Certificates.Kernel.U52.GlueX
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LieType.BorelTits.CompleteFlag

set_option maxRecDepth 400000

namespace CertificateChecks.Batch7768

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.WordF CertificateChecks.KernelU52
  CertificateChecks.KernelU52G

local macro "u52d" : tactic => `(tactic|
  ((repeat' (first
    | apply rPC
    | exact rE _
    | exact cE _
    | exact cPC _ _
    | exact cId)) <;> done))

private theorem invOK : burnsideF48t_u52InvOK () = true := by
  have hL : burnsideF48t_u52LArr.size = 4 := by decide +kernel
  have hG : (burnsideF48t_u52Gens ()).size = 6 := by decide +kernel
  unfold burnsideF48t_u52InvOK
  simp only [burnsideF48t_u52LInv, burnsideF48t_u52GensInv, Array.size_map, hL, hG,
    beq_self_eq_true, Bool.true_and, Bool.and_eq_true]
  refine ⟨CFSG.ONSchreier.allBelowN_iff.2 fun i hi => ?_,
    CFSG.ONSchreier.allBelowN_iff.2 fun i hi => ?_⟩
  · have e := li_eq i hi
    rw [burnsideF48t_u52LInv] at e
    rw [l_eq i hi, e]
    exact pisInv_unpack (allN_spec lpPerm i hi)
  · have e := gi_eq i hi
    rw [burnsideF48t_u52GensInv] at e
    rw [g_eq i hi, e]
    exact pisInv_unpack (gPerm i hi)

private theorem kSift : allN 4 (fun i => siftK 462 9 (mask 9) (462 * 9) (pidn 462 9) CX.LR CX.TRI
    CX.BP 5 0 (LP i)) = true := by
  quickRfl

private theorem lmemOK : burnsideF48t_u52LMemOK () = true := by
  unfold burnsideF48t_u52LMemOK
  refine CFSG.ONSchreier.allBelowN_iff.2 fun i hi => ?_
  rw [l_eq i hi, siftX_eq (canon_of_permOK (allN_spec lpPerm i hi)) (rL i hi).1]
  exact allN_spec kSift i hi

private theorem relOK : burnsideF48t_u52RelOK () = true := by
  unfold burnsideF48t_u52RelOK
  simp (disch := u52d) only [ev_eq, pidE, peqE]
  decide +kernel

private theorem candOK : burnsideF48t_u52CandOK () = true := by
  unfold burnsideF48t_u52CandOK
  simp (disch := u52d) only [ev_eq, pidE, pcE, peqE, allBelowN_eq_allN]
  decide +kernel

private theorem s0_eq : burnsideF48t_u52S0Arr () = (burnsideF48t_u52SW.map fun w =>
    unpack 462 9 (evFK 462 9 (mask 9) (pidn 462 9) LP LPI w)).toArray := by
  simp only [burnsideF48t_u52S0Arr, ev_eq]

private theorem fixOK : burnsideF48t_u52FixOK () = true := by
  unfold burnsideF48t_u52FixOK
  simp only [s0_eq, allBelowN_eq_allN, l_eq 0 (by norm_num), l_eq 1 (by norm_num),
    l_eq 2 (by norm_num), l_eq 3 (by norm_num), getElem!_unpack, List.all_toArray,
    List.any_toArray, List.all_map, List.any_map, Function.comp_def]
  decide +kernel

end CertificateChecks.Batch7768

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ASVolI in
theorem certificate7768 : burnsideF48t_u52InvOK () = true ∧
    burnsideF48t_u52LMemOK () = true ∧
    burnsideF48t_u52RelOK () = true ∧
    burnsideF48t_u52CandOK () = true ∧
    burnsideF48t_u52FixOK () = true :=
  ⟨CertificateChecks.Batch7768.invOK, CertificateChecks.Batch7768.lmemOK, CertificateChecks.Batch7768.relOK, CertificateChecks.Batch7768.candOK, CertificateChecks.Batch7768.fixOK⟩

end Certificates

end
