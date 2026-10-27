
module

public import CFSG.GH74.GLS.C3.Layer2.L5B2
public import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public import CFSG.GH74.GLS.C3.Layer2.L5C0Inputs
meta import Mathlib.GroupTheory.SpecificGroups.Alternating
meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
meta import CFSG.GH74.GLS.C3.Layer2.L5A1
meta import CFSG.GH74.GLS.C3.Layer2.L5B2
meta import CFSG.GH74.GLS.C3.Layer2.L5C0Inputs
import CFSG.Certificates.Kernel.L5.Fast
import CFSG.Certificates.Kernel.L5.Sh0TSound
import CFSG.Certificates.Kernel.L5.HFCIdx
import Certificates.Kernel.L5.Sh0Checks
public import Certificates.Data.Kernel.PermCent.CV
import Certificates.Certificate5065Base
import Mathlib

@[expose] public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open CFSG.Certificates.Kernel
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5051

set_option maxRecDepth 100000

private theorem mem_map_ev_iff (L : List (PkCV.CV 16)) (x : Perm (Fin 16)) :
    x ∈ L.map PkCV.ev ↔ PkCV.cOf x ∈ L := by
  rw [← PkCV.mem_map_ev, PkCV.ev_cOf]

private theorem cv_assoc (a b c : PkCV.CV 16) : a * (b * c) = a * b * c :=
  PkCV.ev_injective (by rw [PkCV.ev_mul, PkCV.ev_mul, PkCV.ev_mul, PkCV.ev_mul, mul_assoc])

private theorem cv_one (a : PkCV.CV 16) : a * 1 = a :=
  PkCV.ev_injective (by rw [PkCV.ev_mul, PkCV.ev_one, mul_one])

private theorem mul_mem_of_closure {M : Type*} [Mul M] [One M] [DecidableEq M]
    (C gens : List M) (k : ℕ) (hassoc : ∀ a b c : M, a * (b * c) = a * b * c)
    (hone : ∀ a : M, a * 1 = a) (hCk : ∀ b ∈ C, b ∈ closureList gens k)
    (h : ∀ x ∈ C, ∀ g ∈ gens, x * g ∈ C) :
    ∀ a ∈ C, ∀ b ∈ C, a * b ∈ C := by
  intro a ha b hb
  have hb' := hCk b hb
  clear hCk hb
  induction k generalizing a b with
  | zero =>
    simp only [closureList, Function.iterate_zero, id, List.mem_singleton] at hb'
    rw [hb', hone]
    exact ha
  | succ k ih =>
    simp only [closureList, Function.iterate_succ_apply'] at hb'
    simp only [closureStep, List.mem_dedup, List.mem_append, List.mem_flatMap,
      List.mem_map] at hb'
    rcases hb' with hb' | ⟨x, hx, g, hg, rfl⟩
    · exact ih a ha b hb'
    · rw [hassoc]
      exact h _ (ih a ha x hx) g hg

private noncomputable def rhoFC (TC : Fin 16 → PkCV.CV 16) (c : PkCV.CV 16) (i : Fin 16) : Fin 16 :=
  ((List.finRange 16).find? fun j => PkCV.eq22C c (TC i) (TC j) c).getD 0

private noncomputable def overV4C (TC : Fin 16 → PkCV.CV 16) (c : PkCV.CV 16) : Bool :=
  v4L.any fun d => (List.finRange 16).all fun i => decide (d i = rhoFC TC c i)

private theorem overV4_ev (Tr : Fin 16 → Perm (Fin 16)) (TC : Fin 16 → PkCV.CV 16)
    (h : ∀ v, Tr v = PkCV.ev (TC v)) : overV4 Tr ∘ PkCV.ev = overV4C TC := by
  funext c
  simp only [Function.comp_apply, overV4, rhoF, overV4C, rhoFC, h, PkCV.ev_inv',
    PkCV.ev_mul', PkCV.decide_ev_eq, PkCV.conj_fast]
  rfl

private noncomputable def T0C (v : Fin 16) : PkCV.CV 16 := PkCV.cOf (tr16 v)

private noncomputable def T1C (v : Fin 16) : PkCV.CV 16 :=
  (tr1L.map PkCV.cOf).getD v.val (PkCV.cOf 1)

private theorem tr1_eq (v : Fin 16) : tr1 v = PkCV.ev (T1C v) := by
  unfold tr1 T1C
  rw [List.getD_map, PkCV.ev_cOf]

private noncomputable def sh0C : List (PkCV.CV 16) := Sh0L.map PkCV.cOf

private noncomputable def s0L0C : List (PkCV.CV 16) := sh0C.filter (overV4C T0C)

private noncomputable def sh1C : List (PkCV.CV 16) := closureList (sh1Gens.map PkCV.cOf) 12

private noncomputable def s0L1C : List (PkCV.CV 16) := sh1C.filter (overV4C T1C)

private theorem sh1L_eq : Sh1L = sh1C.map PkCV.ev := by
  unfold sh1C
  rw [← PkCV.closureList_map_ev, PkCV.map_cOf_ev]
  rfl

private theorem s0L0_eq : S0L0 = s0L0C.map PkCV.ev := by
  unfold S0L0 s0L0C sh0C
  conv_lhs => rw [← PkCV.map_cOf_ev Sh0L]
  rw [List.filter_map, overV4_ev tr16 T0C fun v => (PkCV.ev_cOf _).symm]

private theorem s0L1_eq : S0L1 = s0L1C.map PkCV.ev := by
  unfold S0L1 s0L1C
  rw [sh1L_eq, List.filter_map, overV4_ev tr1 T1C tr1_eq]

private theorem s0L0C_length : s0L0C.length = 64 := by
  decide +kernel

private theorem s0L0C_R1L : ∀ s ∈ R1L, PkCV.cOf s ∈ s0L0C := by
  have h : R1L.all (fun s => decide (PkCV.cOf s ∈ s0L0C)) = true := by
    decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

private theorem s0L0C_RhatL0 : ∀ s ∈ RhatL0, PkCV.cOf s ∈ s0L0C := by
  have h : RhatL0.all (fun s => decide (PkCV.cOf s ∈ s0L0C)) = true := by
    decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

private theorem s0L0C_one : PkCV.cOf 1 ∈ s0L0C := by
  decide +kernel

private theorem s0L0C_mul : mulClosedChkP s0L0C = true := by
  decide +kernel

private theorem s0L0C_inv : invClosedChkP s0L0C = true := by
  decide +kernel

private theorem s0L0C_sub : ∀ c ∈ s0L0C, c ∈ sh0C := by
  decide +kernel

private theorem sh1_chkA :
    (decide sh1C.Nodup &&
    (decide (sh1C.length = 128) &&
    (invClosedChkP sh1C &&
    (allT5.all (fun t => decide (PkCV.cOf (emb48 tr1 yHat1 t) ∈ sh1C)) &&
    RhatL1.all (fun p => decide (PkCV.cOf p ∈ sh1C)))))) = true := by
  decide +kernel

private theorem sh1_chkG :
    sh1C.all (fun x => (sh1Gens.map PkCV.cOf).all fun g => decide (x * g ∈ sh1C)) = true := by
  decide +kernel

private theorem s0L1_chkA :
    (decide (s0L1C.length = 64) &&
    (RhatL1.all (fun s => decide (PkCV.cOf s ∈ s0L1C)) &&
    (decide (PkCV.cOf 1 ∈ s0L1C) &&
    (invClosedChkP s0L1C &&
    s0L1C.all (fun c => decide (c ∈ sh1C)))))) = true := by
  decide +kernel

private theorem s0L1_chkM : mulClosedChkP s0L1C = true := by
  decide +kernel

private theorem sh1_chk :
    sh1C.Nodup ∧
    sh1C.length = 128 ∧
    sh1C.all (fun x => (sh1Gens.map PkCV.cOf).all fun g => decide (x * g ∈ sh1C)) = true ∧
    invClosedChkP sh1C = true ∧
    (∀ t ∈ allT5, PkCV.cOf (emb48 tr1 yHat1 t) ∈ sh1C) ∧
    (∀ p ∈ RhatL1, PkCV.cOf p ∈ sh1C) ∧
    s0L1C.length = 64 ∧
    (∀ s ∈ RhatL1, PkCV.cOf s ∈ s0L1C) ∧
    PkCV.cOf 1 ∈ s0L1C ∧
    mulClosedChkP s0L1C = true ∧
    invClosedChkP s0L1C = true ∧
    (∀ c ∈ s0L1C, c ∈ sh1C) := by
  have hA := sh1_chkA
  have hS := s0L1_chkA
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hA hS
  exact ⟨hA.1, hA.2.1, sh1_chkG, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2, hS.1, hS.2.1, hS.2.2.1,
    s0L1_chkM, hS.2.2.2.1, hS.2.2.2.2⟩

private theorem el16_mem_chk_0 : (List.finRange 16).all (fun i => decide (el16 i ∈ Rml)) = true := by
  decide +kernel

private theorem idx16_el16_chk_1 : (List.finRange 16).all (fun i => decide (idx16 (el16 i) = i)) = true := by
  decide +kernel

private theorem el16_idx16_chk_2 : Rml.all (fun r => decide (el16 (idx16 r) = r)) = true := by
  decide +kernel

private theorem el16_xor_chk_3 : (List.finRange 16).all (fun i => (List.finRange 16).all fun j =>
    decide (el16 (xor16 i j) = el16 i * el16 j)) = true := by
  decide +kernel

private theorem yy5_sq_4 : yy5 * yy5 = 1 := by
  decide +kernel

private theorem T5_cases_chk_5 : allT5.all (fun t => decide (t ∈ Rml ∨ t * yy5 ∈ Rml)) = true := by
  decide +kernel

private theorem actF_yy5_chk_6 : (List.finRange 16).all (fun i => decide (actF yy5 i = yHat i)) = true := by
  decide +kernel

private theorem actF_wm_chk_7 : (List.finRange 16).all (fun i => decide (actF wm i = wHat i)) = true := by
  decide +kernel

private theorem Sh0L_nodup_8 : Sh0L.Nodup := by
  decide +kernel

private theorem Sh0L_length_9 : Sh0L.length = 128 := by
  decide +kernel

private theorem Sh1L_nodup_10 : Sh1L.Nodup := by
  rw [sh1L_eq, PkCV.nodup_map_ev]
  exact sh1_chk.1

private theorem Sh1L_length_11 : Sh1L.length = 128 := by
  rw [sh1L_eq, List.length_map]
  exact sh1_chk.2.1

private theorem Sh0L_mul_chk_12 : mulClosedChkP Sh0L = true := by
  rw [L5S.sh0L_eq, PkCV.mulClosedChkP_map_ev]
  refine L5H.mulClosed_of_tab (n := 128) (mul := L5S.mF) ?_ ?_
  · have h := L5S.sh0L_length
    rwa [L5S.sh0L_eq, List.length_map] at h
  · intro a ha b hb
    obtain ⟨h1, h2⟩ := L5S.mF_spec L5S.sh0Chk_true L5S.sh0C_codes ha hb
    refine ⟨h1, PkCV.ev_injective ?_⟩
    rw [PkCV.ev_mul, ← L5S.sh0L_getD, ← L5S.sh0L_getD, ← L5S.sh0L_getD]
    exact h2

private theorem Sh0L_inv_chk_13 : invClosedChkP Sh0L = true := by
  decide +kernel

private theorem Sh1L_mul_chk_14 : mulClosedChkP Sh1L = true := by
  have hk : ∀ b ∈ sh1C, b ∈ closureList (sh1Gens.map PkCV.cOf) 12 := by
    unfold sh1C
    exact fun _ hb => hb
  have hG := sh1_chk.2.2.1
  simp only [List.all_eq_true, decide_eq_true_eq] at hG
  have hC := mul_mem_of_closure sh1C (sh1Gens.map PkCV.cOf) 12 cv_assoc cv_one hk hG
  rw [sh1L_eq]
  unfold mulClosedChkP
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
  rw [← PkCV.ev_mul]
  exact List.mem_map_of_mem (hC a ha b hb)

private theorem Sh1L_inv_chk_15 : invClosedChkP Sh1L = true := by
  rw [sh1L_eq, PkCV.invClosedChkP_map_ev]
  exact sh1_chk.2.2.2.1

private theorem one_mem_Sh0L_16 : (1 : Perm (Fin 16)) ∈ Sh0L := by
  decide +kernel

private theorem emb48_mul0_chk_17 : allT5.all (fun s => allT5.all fun t =>
    decide (emb48 tr16 yHat (s * t) = emb48 tr16 yHat s * emb48 tr16 yHat t)) = true := by
  decide +kernel

private theorem emb48_mul1_chk_18 : allT5.all (fun s => allT5.all fun t =>
    decide (emb48 tr1 yHat1 (s * t) = emb48 tr1 yHat1 s * emb48 tr1 yHat1 t)) = true := by
  decide +kernel

private theorem emb48_inj0_chk_19 : allT5.all (fun s => allT5.all fun t =>
    imp (decide (emb48 tr16 yHat s = emb48 tr16 yHat t)) (decide (s = t))) = true := by
  decide +kernel

private theorem emb48_inj1_chk_20 : allT5.all (fun s => allT5.all fun t =>
    imp (decide (emb48 tr1 yHat1 s = emb48 tr1 yHat1 t)) (decide (s = t))) = true := by
  decide +kernel

private theorem emb48_mem0_chk_21 : allT5.all (fun t => decide (emb48 tr16 yHat t ∈ Sh0L)) = true := by
  decide +kernel

private theorem emb48_mem1_chk_22 : allT5.all (fun t => decide (emb48 tr1 yHat1 t ∈ Sh1L)) = true := by
  simp only [List.all_eq_true, decide_eq_true_eq, sh1L_eq, mem_map_ev_iff]
  exact sh1_chk.2.2.2.2.1

private theorem S0L0_length_23 : S0L0.length = 64 := by
  rw [s0L0_eq, List.length_map]
  exact s0L0C_length

private theorem S0L1_length_24 : S0L1.length = 64 := by
  rw [s0L1_eq, List.length_map]
  exact sh1_chk.2.2.2.2.2.2.1

private theorem R1L_sub_S0L0_25 : R1L.all (fun s => decide (s ∈ S0L0)) = true := by
  simp only [List.all_eq_true, decide_eq_true_eq, s0L0_eq, mem_map_ev_iff]
  exact s0L0C_R1L

private theorem R1L_length_26 : R1L.length = 16 := by
  decide +kernel

private theorem RhatL0_sub_27 : RhatL0.all (fun s => decide (s ∈ S0L0)) = true := by
  simp only [List.all_eq_true, decide_eq_true_eq, s0L0_eq, mem_map_ev_iff]
  exact s0L0C_RhatL0

private theorem RhatL1_sub_28 : RhatL1.all (fun s => decide (s ∈ S0L1)) = true := by
  simp only [List.all_eq_true, decide_eq_true_eq, s0L1_eq, mem_map_ev_iff]
  exact sh1_chk.2.2.2.2.2.2.2.1

private theorem emb48_one0_29 : emb48 tr16 yHat 1 = 1 := by
  decide +kernel

private theorem emb48_one1_30 : emb48 tr1 yHat1 1 = 1 := by
  decide +kernel

private theorem one_mem_RhatL0_31 : (1 : Perm (Fin 16)) ∈ RhatL0 := by
  decide +kernel

private theorem one_mem_RhatL1_32 : (1 : Perm (Fin 16)) ∈ RhatL1 := by
  decide +kernel

private theorem one_mem_R1L_33 : (1 : Perm (Fin 16)) ∈ R1L := by
  decide +kernel

private theorem one_mem_S0L0_34 : (1 : Perm (Fin 16)) ∈ S0L0 := by
  rw [s0L0_eq, mem_map_ev_iff]
  exact s0L0C_one

private theorem one_mem_S0L1_35 : (1 : Perm (Fin 16)) ∈ S0L1 := by
  rw [s0L1_eq, mem_map_ev_iff]
  exact sh1_chk.2.2.2.2.2.2.2.2.1

private theorem RhatL0_mul_chk_36 : mulClosedChkP RhatL0 = true := by
  decide +kernel

private theorem RhatL0_inv_chk_37 : invClosedChkP RhatL0 = true := by
  decide +kernel

private theorem RhatL1_mul_chk_38 : mulClosedChkP RhatL1 = true := by
  decide +kernel

private theorem RhatL1_inv_chk_39 : invClosedChkP RhatL1 = true := by
  decide +kernel

private theorem R1L_mul_chk_40 : mulClosedChkP R1L = true := by
  decide +kernel

private theorem R1L_inv_chk_41 : invClosedChkP R1L = true := by
  decide +kernel

private theorem S0L0_mul_chk_42 : mulClosedChkP S0L0 = true := by
  rw [s0L0_eq, PkCV.mulClosedChkP_map_ev]
  exact s0L0C_mul

private theorem S0L0_inv_chk_43 : invClosedChkP S0L0 = true := by
  rw [s0L0_eq, PkCV.invClosedChkP_map_ev]
  exact s0L0C_inv

private theorem S0L1_mul_chk_44 : mulClosedChkP S0L1 = true := by
  rw [s0L1_eq, PkCV.mulClosedChkP_map_ev]
  exact sh1_chk.2.2.2.2.2.2.2.2.2.1

private theorem S0L1_inv_chk_45 : invClosedChkP S0L1 = true := by
  rw [s0L1_eq, PkCV.invClosedChkP_map_ev]
  exact sh1_chk.2.2.2.2.2.2.2.2.2.2.1

private theorem RsubP0_le_Sh0_chk_46 : RhatL0.all (fun p => decide (p ∈ Sh0L)) = true := by
  decide +kernel

private theorem RsubP1_le_Sh1_chk_47 : RhatL1.all (fun p => decide (p ∈ Sh1L)) = true := by
  simp only [List.all_eq_true, decide_eq_true_eq, sh1L_eq, mem_map_ev_iff]
  exact sh1_chk.2.2.2.2.2.1

private theorem S0subP0_le_Sh0_chk_48 : S0L0.all (fun p => decide (p ∈ Sh0L)) = true := by
  simp only [List.all_eq_true, decide_eq_true_eq, s0L0_eq, List.forall_mem_map]
  intro c hc
  rw [← PkCV.map_cOf_ev Sh0L, PkCV.mem_map_ev]
  exact s0L0C_sub c hc

private theorem S0subP1_le_Sh1_chk_49 : S0L1.all (fun p => decide (p ∈ Sh1L)) = true := by
  simp only [List.all_eq_true, decide_eq_true_eq, s0L1_eq, sh1L_eq, List.forall_mem_map,
    PkCV.mem_map_ev]
  exact sh1_chk.2.2.2.2.2.2.2.2.2.2.2

private theorem R1subP_le_Sh0_chk_50 : R1L.all (fun p => decide (p ∈ Sh0L)) = true := by
  decide +kernel

private theorem yy5_not_mem_check_51 : yy5 ∈ Rml → False := by
  decide +kernel

private theorem yy5_mem_check_52 : T5b yy5 = true := by
  decide +kernel

private theorem f1_mem_T5_check_53 : T5b f1 = true := by
  decide +kernel

end CertificateChecks.Batch5051

namespace Certificates

end Certificates
