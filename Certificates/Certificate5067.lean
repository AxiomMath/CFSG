module

public import CFSG.GH74.GLS.C3.Layer2.L5C5dInputs
import CFSG.Certificates.Kernel.L5.Sh0TSound
import CFSG.Certificates.Kernel.L5.Sh0ImgSound
import Certificates.Kernel.L5.Sh0Checks
import Certificates.Kernel.L5.Sh0ICls

public section

open CFSG.GH74.GLS.C3.Layer2.L5 CFSG.Certificates.Kernel.L5S

namespace CertificateChecks.Batch5067

open CFSG.GH74.GLS.C3.Layer2.L5 CFSG.Certificates.Kernel.L5S

private theorem genChk_true_0 : genChk = true := by
  rw [genChk_eq sh0Chk_true sh0C_codes]
  decide +kernel

private theorem tF_eq_tP : tF = tP := by
  funext n
  by_cases h : n < 16384
  · exact (beq_iff_eq.mp (List.all_eq_true.mp c5067tP_chk n (List.mem_range.mpr h))).symm
  · simp only [tF, tP, if_neg h]

private theorem iT_eq_iP : iT = iP := by
  funext n
  by_cases h : n < 128
  · exact (beq_iff_eq.mp (List.all_eq_true.mp c5067iP_chk n (List.mem_range.mpr h))).symm
  · simp only [iT, iP, if_neg h]

private theorem wdK_eq_wL : wdK = wL := (beq_iff_eq.mp c5067wL_chk).symm

private theorem tF_lt (n : Nat) : tF n < 128 := by
  unfold tF
  split_ifs with h
  · exact (mF_spec sh0Chk_true sh0C_codes (by omega) (Nat.mod_lt _ (by norm_num))).1
  · norm_num

private theorem RIdxC_lt (r : Nat) (hr : r ∈ RIdxC) : r < 128 := by
  unfold RIdxC at hr
  exact List.mem_range.1 (List.mem_filter.1 hr).1

private theorem classifyK_eq_I (c : Nat) : classifyK c = c5067clsI c := by
  have hb : ∀ n, tP n < 128 := by
    rw [← tF_eq_tP]
    exact tF_lt
  have hl : ∀ y ∈ invLT tP, y < 128 := by
    rw [← tF_eq_tP]
    exact fun y hy => of_decide_eq_true (List.all_eq_true.1 invLK_lt y hy)
  rw [classifyK, c5067clsI, relsK, wdK_eq_wL, tF_eq_tP, iT_eq_iP]
  exact sh0I_all_congr fun x0 hx => by
    rw [classifyRowT_eq_I hb c5067wL_len iP gsK relK RIdxC (invLT tP) 32 xsK ssK (hl x0 hx) hl
      RIdxC_lt]

private theorem classifyChk_true_1 : classifyChk = true :=
  classifyChk_of sh0Chk_true sh0C_codes relK_mem invLK_lt fun c hc => by
    rw [classifyK_eq_I]
    interval_cases c
    exacts [c5067clsI0, c5067clsI1, c5067clsI2, c5067clsI3, c5067clsI4, c5067clsI5, c5067clsI6,
      c5067clsI7, c5067clsI8, c5067clsI9, c5067clsI10, c5067clsI11]

private theorem gamGenChk_true_2 : gamGenChk = true :=
  gamGenChk_of sh0Chk_true sh0C_codes gamGenK_true

end CertificateChecks.Batch5067

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5067 : (genChk = true)
    ∧ (classifyChk = true)
    ∧ (gamGenChk = true) :=
  ⟨CertificateChecks.Batch5067.genChk_true_0, CertificateChecks.Batch5067.classifyChk_true_1, CertificateChecks.Batch5067.gamGenChk_true_2⟩

end Certificates
