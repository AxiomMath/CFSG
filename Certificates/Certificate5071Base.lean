
module

public import CFSG.GH74.GLS.C3.Layer2.L5C9Inputs
import CFSG.GH74.GLS.C3.Layer2.L5C9Base
import CFSG.Certificates.Kernel.L5.HFCIdx
import Certificates.Kernel.L5.HFChecks
import CFSG.Certificates.Kernel.L5.HFQSound
import CFSG.Certificates.Kernel.L5.HFPSound
import CFSG.Certificates.Kernel.L5.HFVSound
import Certificates.Kernel.L5.HFRChecks
public import Certificates.Data.Kernel.PermCent.CV

@[expose] public section

open Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.L5
  CFSG.GH74.GLS.C3.Layer2.L5.HF CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.L5H

namespace CertificateChecks.Batch5071

set_option maxRecDepth 100000

private theorem fam0_card_0 : fam0.card = 4 := by decide +kernel

private theorem fam1_card_1 : fam1.card = 4 := by decide +kernel

private theorem one_mem_n24L_2 : (1 : Perm (Fin 16)) ∈ n24L := by decide +kernel

private theorem n24L_mul_chk_3 : mulClosedChkP n24L = true := by
  rw [← map_cOf_ev n24L, mulClosedChkP_map_ev]
  decide +kernel

private theorem n24L_inv_chk_4 : invClosedChkP n24L = true := by
  rw [← map_cOf_ev n24L, invClosedChkP_map_ev]
  decide +kernel

private theorem n24L_nodup_5 : n24L.Nodup := by
  rw [← map_cOf_ev n24L, nodup_map_ev]
  decide +kernel

private theorem n24L_length_6 : n24L.length = 24 := by decide +kernel

private theorem one_mem_d8L_7 : (1 : Perm (Fin 16)) ∈ d8L := by decide +kernel

private theorem d8L_mul_chk_8 : mulClosedChkP d8L = true := by
  rw [← map_cOf_ev d8L, mulClosedChkP_map_ev]
  decide +kernel

private theorem d8L_inv_chk_9 : invClosedChkP d8L = true := by
  rw [← map_cOf_ev d8L, invClosedChkP_map_ev]
  decide +kernel

private theorem d8L_nodup_10 : d8L.Nodup := by
  rw [← map_cOf_ev d8L, nodup_map_ev]
  decide +kernel

private theorem d8L_length_11 : d8L.length = 8 := by decide +kernel

private theorem yHat_mem_n24L_12 : yHat ∈ n24L := by decide +kernel

private theorem wHat_mem_n24L_13 : wHat ∈ n24L := by decide +kernel

private theorem yHat_mem_d8L_14 : yHat ∈ d8L := by decide +kernel

private theorem d8L_sub_n24L_chk_15 : d8L.all (fun d => decide (d ∈ n24L)) = true := by
  decide +kernel

private theorem v4L_sub_d8L_chk_16 : v4L.all (fun v => decide (v ∈ d8L)) = true := by
  decide +kernel

private theorem v4L_normal_chk_17 :
    n24L.all (fun m => v4L.all fun v => decide (m * v * m⁻¹ ∈ v4L)) = true := by
  decide +kernel

private theorem cHat_v4L_chk_18 : v4L.all (fun v => decide (cHat * v * cHat⁻¹ ∈ v4L)) = true := by
  decide +kernel

private theorem cHat_not_mem_n24L_19 : cHat ∉ n24L := by decide +kernel

private theorem n24L_lin_chk_20 :
    n24L.all (fun A => linChk A && decide (Ppl.image A = Ppl)) = true := by
  decide +kernel

private theorem twPerm_lin_21 : IsLin16 twPerm := isLin16_of_chk (by decide +kernel)

private theorem twPerm_Ppl_22 : Ppl.image twPerm = Ppl := by decide +kernel

private theorem twPerm_Qpl_23 : Qpl.image twPerm = Qpl := by decide +kernel

private theorem twPerm_fam0_24 : fam0.image (fun V => V.image twPerm) = fam1 := by decide +kernel

private theorem twPerm_fam1_25 : fam1.image (fun V => V.image twPerm) = fam0 := by decide +kernel

private theorem twPerm_yHat_26 : twPerm * yHat * twPerm⁻¹ = yHat := by decide +kernel

private theorem twPerm_wHat_27 : twPerm * wHat = wHat * twPerm := by decide +kernel

private theorem actF_gTw_chk_28 :
    (List.finRange 16).all (fun i => decide (actF gTw i = twPerm i)) = true := by
  decide +kernel

private theorem n24_enum_29 : allQ2 gN n24Entry = true := by
  rw [allQ2_eq]
  simp only [n24Entry_ev G72TabK G72K]
  obtain ⟨hG, hM⟩ := g72Pin G72PinK
  have hc : n24EntryV g72GN g72MP = n24EntryC :=
    funext fun x => by rw [n24EntryV_eq, hG, hM, n24EntryN_eq]
  have e : ∀ k, CFSG.Certificates.Kernel.L5Q.c5071n24Row k =
      CFSG.Certificates.Kernel.L5Q.rowQ gN n24EntryC k := fun _ => by rw [← hc]; rfl
  refine allQ2C_of_rows _ _ fun k hk => CFSG.Certificates.Kernel.L5Q.rowQ_sound ?_
  rw [← e]
  interval_cases k
  exacts [CFSG.Certificates.Kernel.L5Q.c5071n24Row0, CFSG.Certificates.Kernel.L5Q.c5071n24Row1,
    CFSG.Certificates.Kernel.L5Q.c5071n24Row2, CFSG.Certificates.Kernel.L5Q.c5071n24Row3]

private theorem fam0_img (m : Perm (Fin 16)) (h : fam0ChkN (cOf m) = true) :
    ∀ V ∈ fam0, V.image m ∈ fam0 := by
  have := fam0_of_chkN (cOf m) h
  rwa [ev_cOf] at this

private theorem fam1_img (m : Perm (Fin 16)) (h : fam1ChkN (cOf m) = true) :
    ∀ V ∈ fam1, V.image m ∈ fam1 := by
  have := fam1_of_chkN (cOf m) h
  rwa [ev_cOf] at this

private theorem n24_gen_hyps_fam0_30 : ∃ m : Perm (Fin 16), IsLin16 m ∧ Qpl.image m ≠ Qpl ∧
    Qpl.image m ∩ Qpl = {0} ∧ Qpl.image m ∩ Ppl = {0} ∧
      ∀ V ∈ fam0, V.image yHat ∈ fam0 ∧ V.image wHat ∈ fam0 ∧ V.image m ∈ fam0 := by
  have hy := fam0_img yHat (by decide +kernel)
  have hw := fam0_img wHat (by decide +kernel)
  have hm := fam0_img (n24L.getD 6 1) (by decide +kernel)
  exact ⟨n24L.getD 6 1, isLin16_of_chk (by decide +kernel), by decide +kernel, by decide +kernel,
    by decide +kernel, fun V hV => ⟨hy V hV, hw V hV, hm V hV⟩⟩

private theorem n24_gen_hyps_fam1_31 : ∃ m : Perm (Fin 16), IsLin16 m ∧ Qpl.image m ≠ Qpl ∧
    Qpl.image m ∩ Qpl = {0} ∧ Qpl.image m ∩ Ppl = {0} ∧
      ∀ V ∈ fam1, V.image yHat ∈ fam1 ∧ V.image wHat ∈ fam1 ∧ V.image m ∈ fam1 := by
  have hy := fam1_img yHat (by decide +kernel)
  have hw := fam1_img wHat (by decide +kernel)
  have hm := fam1_img (twPerm * n24L.getD 6 1 * twPerm⁻¹) (by decide +kernel)
  exact ⟨twPerm * n24L.getD 6 1 * twPerm⁻¹, isLin16_of_chk (by decide +kernel), by decide +kernel,
    by decide +kernel, by decide +kernel, fun V hV => ⟨hy V hV, hw V hV, hm V hV⟩⟩

private theorem Qpl_mem_fam0_36 : Qpl ∈ fam0 := by decide +kernel

private theorem Qpl_mem_fam1_37 : Qpl ∈ fam1 := by decide +kernel

private theorem G72L_length_38 : G72L.length = 72 := by
  rw [G72L_eq, List.length_map]
  exact (G72tab_facts G72TabK).1

private theorem G72L_nodup_39 : G72L.Nodup := by
  rw [G72L_eq, nodup_map_ev]
  exact (G72tab_facts G72TabK).2.1

private theorem one_mem_G72L_40 : (1 : Perm (Fin 16)) ∈ G72L := by
  rw [G72L_eq, one_eq_ev, mem_map_ev]
  exact (G72tab_facts G72TabK).2.2.1

private theorem G72L_mul_chk_41 : mulClosedChkP G72L = true := by
  rw [G72L_eq, mulClosedChkP_map_ev]
  exact G72C_mul G72TabK

private theorem G72L_inv_chk_42 : invClosedChkP G72L = true := by
  rw [G72L_eq, invClosedChkP_map_ev]
  exact (G72chk_facts G72K).1

private theorem G72L_facts_43 : G72L.all (fun m => linChk m && fam0Chk m) = true := by
  rw [G72L_eq, List.all_map]
  simp only [Function.comp_def, linChk_ev, fam0Chk_ev]
  exact G72LinK

private theorem fam_enum_44 : allQ2 gFam (famEntry G72L) = true := by
  rw [allQ2_eq]
  simp only [famEntry_eq G72TabK G72K]
  obtain ⟨hG, hM⟩ := g72Pin G72PinK
  have hc : famEntryN g72GN g72MP = famEntryC := funext fun x => by rw [hG, hM, famEntryN_eq]
  have e : ∀ k, CFSG.Certificates.Kernel.L5Q.c5071famRow k =
      CFSG.Certificates.Kernel.L5Q.rowQ gFam famEntryC k := fun _ => by rw [← hc]; rfl
  refine allQ2C_of_rows _ _ fun k hk => CFSG.Certificates.Kernel.L5Q.rowQ_sound ?_
  rw [← e]
  interval_cases k
  exacts [CFSG.Certificates.Kernel.L5Q.c5071famRow0, CFSG.Certificates.Kernel.L5Q.c5071famRow1,
    CFSG.Certificates.Kernel.L5Q.c5071famRow2, CFSG.Certificates.Kernel.L5Q.c5071famRow3]

private theorem n24_le_G72_chk_45 : n24L.all (fun A => decide (A ∈ G72L)) = true := by
  rw [G72L_eq, n24L_eq, List.all_map]
  simp only [Function.comp_def, decide_mem_map_ev]
  exact List.all_eq_true.2 fun a ha => decide_eq_true ((G72chk_facts G72K).2.1 a ha)

private theorem cHat_mem_G72L_46 : cHat ∈ G72L := by
  have e : cHat = ev cHC := by rw [cHC, ev_cOf]
  rw [G72L_eq, e, mem_map_ev]
  exact (G72chk_facts G72K).2.2.2.2.1

private theorem n24g_mem_47 : n24L.getD 6 1 ∈ n24L := by decide +kernel

private theorem yHat_ne_one_48 : yHat ≠ 1 := by decide +kernel

private theorem d8_enum_49 : n24L.all (fun b => n24L.all fun c => d8Chk b c) = true :=
  d8_enum_of n24TabK d8K

end CertificateChecks.Batch5071

namespace Certificates

end Certificates
