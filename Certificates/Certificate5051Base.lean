
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

private theorem s0L0C_inv : invClosedChkP s0L0C = true := by
  decide +kernel

private theorem s0L0C_sub : ∀ c ∈ s0L0C, c ∈ sh0C := by
  decide +kernel

private noncomputable def c51Gens : List (PkCV.CV 16) := sh1Gens.map PkCV.cOf

private noncomputable def c51Word (w : List ℕ) : PkCV.CV 16 :=
  w.foldl (fun a k => a * c51Gens.getD k 1) 1

private def c51RepW : List (List ℕ) :=
  [[], [4], [5], [4, 5], [5, 4], [4, 5, 4], [5, 4, 5], [4, 5, 4, 5]]

private def c51BitW : List (List ℕ) :=
  [[], [0], [1], [0, 1], [2], [0, 2], [1, 2], [0, 1, 2], [3], [0, 3], [1, 3], [0, 1, 3], [2, 3],
    [0, 2, 3], [1, 2, 3], [0, 1, 2, 3]]

private def c51W : List (List ℕ) := c51BitW.flatMap fun b => c51RepW.map (b ++ ·)

private noncomputable def c51Sh1 : List (PkCV.CV 16) :=
  (List.finRange 16).flatMap fun v => c51RepW.map fun r => T1C v * c51Word r

private noncomputable def c51S0 : List (PkCV.CV 16) :=
  (List.finRange 16).flatMap fun v =>
    [[], [5], [4, 5, 4], [4, 5, 4, 5]].map fun r => T1C v * c51Word r

private theorem mem_closureList_succ {M : Type*} [Mul M] [One M] [DecidableEq M] (gens : List M)
    (k : ℕ) {x : M} (hx : x ∈ closureList gens k) : x ∈ closureList gens (k + 1) := by
  simp only [closureList, Function.iterate_succ_apply', closureStep, List.mem_dedup,
    List.mem_append]
  exact Or.inl hx

private theorem mem_closureList_le {M : Type*} [Mul M] [One M] [DecidableEq M] (gens : List M)
    {j m : ℕ} (hjm : j ≤ m) {x : M} (hx : x ∈ closureList gens j) : x ∈ closureList gens m := by
  induction m, hjm using Nat.le_induction with
  | base => exact hx
  | succ m _ ih => exact mem_closureList_succ gens m ih

private theorem mem_closureList_foldl {M : Type*} [Mul M] [One M] [DecidableEq M]
    (gens : List M) (w : List ℕ) (hw : ∀ k ∈ w, k < gens.length) :
    ∀ (j : ℕ) (a : M), a ∈ closureList gens j →
      w.foldl (fun a k => a * gens.getD k 1) a ∈ closureList gens (j + w.length) := by
  induction w with
  | nil => intro j a ha; simpa using ha
  | cons k w ih =>
    intro j a ha
    have hk : gens.getD k 1 ∈ gens := by
      rw [List.getD_eq_getElem _ _ (hw k List.mem_cons_self)]
      exact List.getElem_mem _
    have h1 : a * gens.getD k 1 ∈ closureList gens (j + 1) := by
      simp only [closureList, Function.iterate_succ_apply', closureStep, List.mem_dedup,
        List.mem_append, List.mem_flatMap, List.mem_map]
      exact Or.inr ⟨a, ha, _, hk, rfl⟩
    have := ih (fun k' hk' => hw k' (List.mem_cons_of_mem _ hk')) (j + 1) _ h1
    rw [List.foldl_cons, List.length_cons]
    rwa [Nat.add_assoc, Nat.add_comm 1] at this

private theorem closureList_sub {M : Type*} [Mul M] [One M] [DecidableEq M] (gens L : List M)
    (h1 : 1 ∈ L) (hg : ∀ x ∈ L, ∀ g ∈ gens, x * g ∈ L) :
    ∀ k, ∀ x ∈ closureList gens k, x ∈ L := by
  intro k
  induction k with
  | zero =>
    intro x hx
    simp only [closureList, Function.iterate_zero, id, List.mem_singleton] at hx
    rw [hx]
    exact h1
  | succ k ih =>
    intro x hx
    simp only [closureList, Function.iterate_succ_apply'] at hx
    simp only [closureStep, List.mem_dedup, List.mem_append, List.mem_flatMap,
      List.mem_map] at hx
    rcases hx with hx | ⟨y, hy, g, hg', rfl⟩
    · exact ih x hx
    · exact hg y (ih y hy) g hg'

private theorem c51_cl_nodup {M : Type*} [Mul M] [One M] [DecidableEq M] (gens : List M)
    (k : ℕ) : (closureList gens (k + 1)).Nodup := by
  simp only [closureList, Function.iterate_succ_apply', closureStep]
  exact List.nodup_dedup _

private theorem mulClosedChkP_congr {l l' : List (PkCV.CV 16)} (h : ∀ x, x ∈ l ↔ x ∈ l') :
    mulClosedChkP l = mulClosedChkP l' := by
  unfold mulClosedChkP
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, decide_eq_true_eq, h]

private theorem invClosedChkP_congr {l l' : List (PkCV.CV 16)} (h : ∀ x, x ∈ l ↔ x ∈ l') :
    invClosedChkP l = invClosedChkP l' := by
  unfold invClosedChkP
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, decide_eq_true_eq, h]

private theorem c51_words :
    (decide (c51Sh1 = c51W.map c51Word) &&
    c51W.all (fun w => decide (w.length ≤ 12) && w.all fun k => decide (k < 6))) = true := by
  decide +kernel

private theorem c51_chkA :
    (decide c51Sh1.Nodup &&
    (decide (c51Sh1.length = 128) &&
    (decide (1 ∈ c51Sh1) &&
    (invClosedChkP c51Sh1 &&
    ((List.finRange 16).all (fun i => decide (T1C i * PkCV.cOf yHat1 ∈ c51Sh1)) &&
    RhatL1.all (fun p => decide (PkCV.cOf p ∈ c51Sh1))))))) = true := by
  decide +kernel

private theorem c51_chkG :
    c51Sh1.all (fun x => c51Gens.all fun g => decide (x * g ∈ c51Sh1)) = true := by
  decide +kernel

private theorem c51_chkS :
    (decide (c51Sh1.filter (overV4C T1C) = c51S0) &&
    (decide (c51S0.length = 64) &&
    (RhatL1.all (fun s => decide (PkCV.cOf s ∈ c51S0)) &&
    (decide (PkCV.cOf 1 ∈ c51S0) &&
    invClosedChkP c51S0)))) = true := by
  decide +kernel

private noncomputable def c51G0 : List (PkCV.CV 16) :=
  c51Gens.take 4 ++ [c51Word [5], c51Word [4, 5, 4]]

private noncomputable def c51Word0 (w : List ℕ) : PkCV.CV 16 :=
  w.foldl (fun a k => a * c51G0.getD k 1) 1

private def c51W0 : List (List ℕ) := c51BitW.flatMap fun b => [[], [4], [5], [5, 4]].map (b ++ ·)

private theorem c51_chkM0 :
    (decide (c51S0 = c51W0.map c51Word0) &&
    (c51W0.all (fun w => w.all fun k => decide (k < 6)) &&
    c51S0.all (fun x => c51G0.all fun g => decide (x * g ∈ c51S0)))) = true := by
  decide +kernel

private theorem foldl_mul_left (gs : List (PkCV.CV 16)) (w : List ℕ) :
    ∀ a c : PkCV.CV 16, a * w.foldl (fun a k => a * gs.getD k 1) c =
      w.foldl (fun a k => a * gs.getD k 1) (a * c) := by
  induction w with
  | nil => intro a c; rfl
  | cons k w ih =>
    intro a c
    rw [List.foldl_cons, List.foldl_cons, ih, cv_assoc]

private theorem c51_foldl_mem (gs L : List (PkCV.CV 16)) (hg : ∀ x ∈ L, ∀ g ∈ gs, x * g ∈ L)
    (w : List ℕ) (hw : ∀ k ∈ w, k < gs.length) :
    ∀ a ∈ L, w.foldl (fun a k => a * gs.getD k 1) a ∈ L := by
  induction w with
  | nil => intro a ha; exact ha
  | cons k w ih =>
    intro a ha
    rw [List.foldl_cons]
    refine ih (fun k' hk' => hw k' (List.mem_cons_of_mem _ hk')) _ (hg a ha _ ?_)
    rw [List.getD_eq_getElem _ _ (hw k List.mem_cons_self)]
    exact List.getElem_mem _

private theorem c51_mulClosed (L G : List (PkCV.CV 16)) (W : List (List ℕ))
    (hW : L = W.map fun w => w.foldl (fun a k => a * G.getD k 1) 1)
    (hk : ∀ w ∈ W, ∀ k ∈ w, k < G.length) (hg : ∀ x ∈ L, ∀ g ∈ G, x * g ∈ L) :
    mulClosedChkP L = true := by
  unfold mulClosedChkP
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro a ha b hb
  rw [hW, List.mem_map] at hb
  obtain ⟨w, hw, rfl⟩ := hb
  rw [foldl_mul_left, cv_one]
  exact c51_foldl_mem G L hg w (hk w hw) a ha

private theorem c51_chkM : mulClosedChkP c51S0 = true := by
  have h := c51_chkM0
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hW, hk, hg⟩ := h
  refine c51_mulClosed c51S0 c51G0 c51W0 hW (fun w hw k hk'' => ?_) hg
  have := hk w hw k hk''
  simpa [c51G0, c51Gens, sh1Gens] using this

private noncomputable def c51G00 : List (PkCV.CV 16) :=
  [T0C 1, T0C 2, T0C 4, T0C 8, PkCV.cOf (d8L.getD 3 1), PkCV.cOf (d8L.getD 4 1)]

private noncomputable def c51T0 : List (PkCV.CV 16) :=
  (List.finRange 16).flatMap fun v =>
    [0, 3, 4, 7].map fun i => T0C v * PkCV.cOf (d8L.getD i 1)

private def c51W00 : List (List ℕ) := c51BitW.flatMap fun b => [[], [4], [5], [4, 5]].map (b ++ ·)

private theorem c51_chkM00 :
    (decide (s0L0C = c51T0) &&
    (decide (c51T0 = c51W00.map fun w => w.foldl (fun a k => a * c51G00.getD k 1) 1) &&
    (c51W00.all (fun w => w.all fun k => decide (k < 6)) &&
    c51T0.all (fun x => c51G00.all fun g => decide (x * g ∈ c51T0))))) = true := by
  decide +kernel

private theorem s0L0C_mul : mulClosedChkP s0L0C = true := by
  have h := c51_chkM00
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨h0, hW, hk, hg⟩ := h
  rw [h0]
  refine c51_mulClosed c51T0 c51G00 c51W00 hW (fun w hw k hk'' => ?_) hg
  have := hk w hw k hk''
  simpa [c51G00] using this

private theorem sh1C_mem (x : PkCV.CV 16) : x ∈ sh1C ↔ x ∈ c51Sh1 := by
  have hA := c51_chkA
  have hW := c51_words
  have hG := c51_chkG
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hA hW hG
  constructor
  · intro hx
    exact closureList_sub _ _ hA.2.2.1 hG 12 x hx
  · intro hx
    rw [hW.1, List.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    have hl := (hW.2 w hw).1
    have hk : ∀ k ∈ w, k < c51Gens.length := fun k hk => by
      simpa [c51Gens, sh1Gens] using (hW.2 w hw).2 k hk
    have h1 : (1 : PkCV.CV 16) ∈ closureList c51Gens 0 := by simp [closureList]
    have := mem_closureList_foldl c51Gens w hk 0 1 h1
    rw [Nat.zero_add] at this
    exact mem_closureList_le c51Gens hl this

private theorem sh1C_perm : sh1C.Perm c51Sh1 := by
  have hA := c51_chkA
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hA
  exact (List.perm_ext_iff_of_nodup (c51_cl_nodup _ 11) hA.1).2 sh1C_mem

private theorem s0L1C_perm : s0L1C.Perm c51S0 := by
  have hS := c51_chkS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hS
  rw [← hS.1]
  exact sh1C_perm.filter _

private theorem s0L1C_mem (x : PkCV.CV 16) : x ∈ s0L1C ↔ x ∈ c51S0 := s0L1C_perm.mem_iff

private theorem c51_hA : c51Sh1.Nodup ∧ c51Sh1.length = 128 ∧ 1 ∈ c51Sh1 ∧
    invClosedChkP c51Sh1 = true ∧
    (∀ i ∈ List.finRange 16, T1C i * PkCV.cOf yHat1 ∈ c51Sh1) ∧
    (∀ p ∈ RhatL1, PkCV.cOf p ∈ c51Sh1) := by
  have hA := c51_chkA
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hA
  exact hA

private theorem c51_hS : c51Sh1.filter (overV4C T1C) = c51S0 ∧ c51S0.length = 64 ∧
    (∀ s ∈ RhatL1, PkCV.cOf s ∈ c51S0) ∧ PkCV.cOf 1 ∈ c51S0 ∧ invClosedChkP c51S0 = true := by
  have hS := c51_chkS
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hS
  exact hS

private theorem c51_e1 : sh1C.Nodup := c51_cl_nodup (sh1Gens.map PkCV.cOf) 11

private theorem c51_e2 : sh1C.length = 128 := sh1C_perm.length_eq.trans c51_hA.2.1

private theorem c51_e3 :
    sh1C.all (fun x => (sh1Gens.map PkCV.cOf).all fun g => decide (x * g ∈ sh1C)) = true := by
  have hG := c51_chkG
  simp only [List.all_eq_true, decide_eq_true_eq] at hG ⊢
  intro x hx g hg
  exact (sh1C_mem _).2 (hG x ((sh1C_mem _).1 hx) g hg)

private theorem c51_e4 : invClosedChkP sh1C = true :=
  (invClosedChkP_congr sh1C_mem).trans c51_hA.2.2.2.1

private theorem c51_e5 (i : Fin 16) : PkCV.cOf (tr1 i * yHat1) ∈ sh1C := by
  have h : PkCV.cOf (tr1 i * yHat1) = T1C i * PkCV.cOf yHat1 :=
    PkCV.ev_injective (by rw [PkCV.ev_cOf, PkCV.ev_mul, PkCV.ev_cOf, tr1_eq])
  rw [h]
  exact (sh1C_mem _).2 (c51_hA.2.2.2.2.1 i (List.mem_finRange i))

private theorem c51_e6 : ∀ p ∈ RhatL1, PkCV.cOf p ∈ sh1C :=
  fun p hp => (sh1C_mem _).2 (c51_hA.2.2.2.2.2 p hp)

private theorem c51_e7 : s0L1C.length = 64 := s0L1C_perm.length_eq.trans c51_hS.2.1

private theorem c51_e8 : ∀ s ∈ RhatL1, PkCV.cOf s ∈ s0L1C :=
  fun s hs => (s0L1C_mem _).2 (c51_hS.2.2.1 s hs)

private theorem c51_e9 : PkCV.cOf 1 ∈ s0L1C := (s0L1C_mem _).2 c51_hS.2.2.2.1

private theorem c51_e10 : mulClosedChkP s0L1C = true :=
  (mulClosedChkP_congr s0L1C_mem).trans c51_chkM

private theorem c51_e11 : invClosedChkP s0L1C = true :=
  (invClosedChkP_congr s0L1C_mem).trans c51_hS.2.2.2.2

private theorem c51_e12 : ∀ c ∈ s0L1C, c ∈ sh1C := by
  intro c hc
  unfold s0L1C at hc
  exact List.mem_of_mem_filter hc

private theorem sh1_chk :
    sh1C.Nodup ∧
    sh1C.length = 128 ∧
    sh1C.all (fun x => (sh1Gens.map PkCV.cOf).all fun g => decide (x * g ∈ sh1C)) = true ∧
    invClosedChkP sh1C = true ∧
    (∀ i : Fin 16, PkCV.cOf (tr1 i * yHat1) ∈ sh1C) ∧
    (∀ p ∈ RhatL1, PkCV.cOf p ∈ sh1C) ∧
    s0L1C.length = 64 ∧
    (∀ s ∈ RhatL1, PkCV.cOf s ∈ s0L1C) ∧
    PkCV.cOf 1 ∈ s0L1C ∧
    mulClosedChkP s0L1C = true ∧
    invClosedChkP s0L1C = true ∧
    (∀ c ∈ s0L1C, c ∈ sh1C) :=
  ⟨c51_e1, c51_e2, c51_e3, c51_e4, c51_e5, c51_e6, c51_e7, c51_e8, c51_e9, c51_e10, c51_e11,
    c51_e12⟩

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
  rw [L5S.sh0L_eq]
  exact List.Nodup.of_map _ L5S.sh0C_codes

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
  unfold invClosedChkP
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hx
  have ha' : a < 128 := by rwa [L5S.sh0L_length] at ha
  obtain ⟨h1, h2⟩ := L5S.iF_spec L5S.sh0Chk_true L5S.sh0C_codes ha'
  rw [← List.getD_eq_getElem Sh0L 1 ha, h2,
    List.getD_eq_getElem _ _ (by rwa [L5S.sh0L_length])]
  exact List.getElem_mem _

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

private theorem RhatL0_inv_chk_37 : invClosedChkP RhatL0 = true := by
  decide +kernel

private theorem RhatL1_inv_chk_39 : invClosedChkP RhatL1 = true := by
  decide +kernel

private theorem R1L_mul_chk_40 : mulClosedChkP R1L = true := by
  rw [← PkCV.map_cOf_ev R1L, PkCV.mulClosedChkP_map_ev]
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

private theorem c51_yE_chk :
    (List.finRange 16).all (fun j => decide (yy5 * el16 j = el16 (yHat j) * yy5)) = true := by
  decide +kernel

private theorem c51_E_xor (i j : Fin 16) : el16 (xor16 i j) = el16 i * el16 j := by
  have h := el16_xor_chk_3
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h i (List.mem_finRange i) j (List.mem_finRange j)

private theorem c51_E_mem (i : Fin 16) : el16 i ∈ Rml := by
  have h := el16_mem_chk_0
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h i (List.mem_finRange i)

private theorem c51_idxE (i : Fin 16) : idx16 (el16 i) = i := by
  have h := idx16_el16_chk_1
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h i (List.mem_finRange i)

private theorem c51_Eidx {r : Amb 5} (hr : r ∈ Rml) : el16 (idx16 r) = r := by
  have h := el16_idx16_chk_2
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h r hr

private theorem c51_yE (j : Fin 16) : yy5 * el16 j = el16 (yHat j) * yy5 := by
  have h := c51_yE_chk
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h j (List.mem_finRange j)

private theorem c51_E_sq (i : Fin 16) : el16 i * el16 i = 1 := by
  have h0 := c51_E_xor 0 0
  have hx : xor16 0 0 = 0 := by decide
  rw [hx] at h0
  have h1 : el16 0 = 1 := mul_left_cancel (h0.symm.trans (mul_one _).symm)
  have hi : xor16 i i = 0 := Fin.ext (by simp [xor16])
  rw [← c51_E_xor, hi, h1]

private theorem c51_Ey_nmem (i : Fin 16) : el16 i * yy5 ∉ Rml := by
  intro h
  apply yy5_not_mem_check_51
  have : yy5 = el16 (xor16 i (idx16 (el16 i * yy5))) := by
    rw [c51_E_xor, c51_Eidx h, ← mul_assoc, c51_E_sq, one_mul]
  rw [this]
  exact c51_E_mem _

private theorem c51_form {t : Amb 5} (ht : t ∈ allT5) :
    (∃ i, t = el16 i) ∨ ∃ i, t = el16 i * yy5 := by
  have h := T5_cases_chk_5
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  rcases h t ht with h | h
  · exact Or.inl ⟨idx16 t, (c51_Eidx h).symm⟩
  · refine Or.inr ⟨idx16 (t * yy5), ?_⟩
    rw [c51_Eidx h, mul_assoc, yy5_sq_4, mul_one]

section Emb

variable (Tr : Fin 16 → Perm (Fin 16)) (yy : Perm (Fin 16))

private theorem c51_emb_E (i : Fin 16) : emb48 Tr yy (el16 i) = Tr i := by
  unfold emb48
  rw [ite_eq_left (c51_E_mem i), c51_idxE]

private theorem c51_emb_Ey (i : Fin 16) : emb48 Tr yy (el16 i * yy5) = Tr i * yy := by
  unfold emb48
  rw [ite_eq_right (c51_Ey_nmem i), mul_assoc, yy5_sq_4, mul_one, c51_idxE]

private theorem c51_emb_mul (hT : ∀ i j, Tr (xor16 i j) = Tr i * Tr j)
    (hY : ∀ j, yy * Tr j = Tr (yHat j) * yy) (hyy : yy * yy = 1) :
    ∀ s ∈ allT5, ∀ t ∈ allT5, emb48 Tr yy (s * t) = emb48 Tr yy s * emb48 Tr yy t := by
  intro s hs t ht
  rcases c51_form hs with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rcases c51_form ht with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [← c51_E_xor, c51_emb_E, c51_emb_E, c51_emb_E, hT]
  · rw [← mul_assoc, ← c51_E_xor, c51_emb_Ey, c51_emb_E, c51_emb_Ey, hT, mul_assoc]
  · have h : el16 i * yy5 * el16 j = el16 (xor16 i (yHat j)) * yy5 := by
      rw [mul_assoc, c51_yE, ← mul_assoc, c51_E_xor]
    rw [h, c51_emb_Ey, c51_emb_Ey, c51_emb_E, hT, mul_assoc (Tr i) yy, hY, mul_assoc]
  · have h : el16 i * yy5 * (el16 j * yy5) = el16 (xor16 i (yHat j)) := by
      rw [mul_assoc (el16 i), ← mul_assoc yy5, c51_yE, mul_assoc (el16 (yHat j)), yy5_sq_4,
        mul_one, c51_E_xor]
    rw [h, c51_emb_E, c51_emb_Ey, c51_emb_Ey, hT, mul_assoc (Tr i) yy, ← mul_assoc yy, hY,
      mul_assoc (Tr (yHat j)), hyy, mul_one]

private theorem c51_emb_inj (hI : ∀ i j, Tr i = Tr j → i = j) (hI2 : ∀ i j, Tr i ≠ Tr j * yy) :
    ∀ s ∈ allT5, ∀ t ∈ allT5, emb48 Tr yy s = emb48 Tr yy t → s = t := by
  intro s hs t ht
  rcases c51_form hs with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rcases c51_form ht with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [c51_emb_E, c51_emb_E]
    intro h
    rw [hI i j h]
  · rw [c51_emb_E, c51_emb_Ey]
    exact fun h => absurd h (hI2 i j)
  · rw [c51_emb_Ey, c51_emb_E]
    exact fun h => absurd h.symm (hI2 j i)
  · rw [c51_emb_Ey, c51_emb_Ey]
    intro h
    rw [hI i j (mul_right_cancel h)]

end Emb

private noncomputable def c51HomChk (TC : Fin 16 → PkCV.CV 16) (YC : PkCV.CV 16) : Bool :=
  decide (YC * YC = 1) &&
  ((List.finRange 16).all (fun j => decide (YC * TC j = TC (yHat j) * YC)) &&
  (List.finRange 16).all fun i => (List.finRange 16).all fun j =>
    decide (TC (xor16 i j) = TC i * TC j) && (decide (TC i = TC j → i = j) &&
    !decide (TC i = TC j * YC)))

private theorem c51_hyps (Tr : Fin 16 → Perm (Fin 16)) (yy : Perm (Fin 16))
    (TC : Fin 16 → PkCV.CV 16) (YC : PkCV.CV 16) (hTr : ∀ v, Tr v = PkCV.ev (TC v))
    (hyy : yy = PkCV.ev YC) (hc : c51HomChk TC YC = true) :
    (∀ i j, Tr (xor16 i j) = Tr i * Tr j) ∧ (∀ j, yy * Tr j = Tr (yHat j) * yy) ∧
    yy * yy = 1 ∧ (∀ i j, Tr i = Tr j → i = j) ∧ (∀ i j, Tr i ≠ Tr j * yy) := by
  unfold c51HomChk at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hc
  obtain ⟨h1, h2, h3⟩ := hc
  have m := List.mem_finRange (n := 16)
  refine ⟨fun i j => ?_, fun j => ?_, ?_, fun i j h => ?_, fun i j h => ?_⟩
  · rw [hTr, hTr, hTr, ← PkCV.ev_mul, (h3 i (m i) j (m j)).1]
  · rw [hTr, hTr, hyy, ← PkCV.ev_mul, ← PkCV.ev_mul, h2 j (m j)]
  · rw [hyy, ← PkCV.ev_mul, h1, PkCV.ev_one]
  · rw [hTr, hTr] at h
    exact (h3 i (m i) j (m j)).2.1 (PkCV.ev_injective h)
  · rw [hTr, hTr, hyy, ← PkCV.ev_mul] at h
    exact (h3 i (m i) j (m j)).2.2 (PkCV.ev_injective h)

private theorem c51_emb (Tr : Fin 16 → Perm (Fin 16)) (yy : Perm (Fin 16))
    (TC : Fin 16 → PkCV.CV 16) (YC : PkCV.CV 16) (hTr : ∀ v, Tr v = PkCV.ev (TC v))
    (hyy : yy = PkCV.ev YC) (hc : c51HomChk TC YC = true) :
    (∀ s ∈ allT5, ∀ t ∈ allT5, emb48 Tr yy (s * t) = emb48 Tr yy s * emb48 Tr yy t) ∧
    (∀ s ∈ allT5, ∀ t ∈ allT5, emb48 Tr yy s = emb48 Tr yy t → s = t) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := c51_hyps Tr yy TC YC hTr hyy hc
  exact ⟨c51_emb_mul Tr yy h1 h2 h3, c51_emb_inj Tr yy h4 h5⟩

private theorem c51_mulTr (Tr : Fin 16 → Perm (Fin 16))
    (hT : ∀ i j, Tr (xor16 i j) = Tr i * Tr j) :
    mulClosedChkP ((List.finRange 16).map Tr) = true := by
  unfold mulClosedChkP
  simp only [List.all_eq_true, decide_eq_true_eq, List.forall_mem_map]
  intro i _ j _
  rw [← hT]
  exact List.mem_map_of_mem (List.mem_finRange _)

private theorem c51_emb_form (Tr : Fin 16 → Perm (Fin 16)) (yy : Perm (Fin 16)) {t : Amb 5}
    (ht : t ∈ allT5) : ∃ i, emb48 Tr yy t = Tr i ∨ emb48 Tr yy t = Tr i * yy := by
  rcases c51_form ht with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact ⟨i, Or.inl (c51_emb_E Tr yy i)⟩
  · exact ⟨i, Or.inr (c51_emb_Ey Tr yy i)⟩

private theorem c51_hom0 : c51HomChk T0C (PkCV.cOf yHat) = true := by
  decide +kernel

private theorem c51_hom1 : c51HomChk T1C (PkCV.cOf yHat1) = true := by
  decide +kernel

private theorem c51_emb0 :
    (∀ s ∈ allT5, ∀ t ∈ allT5, emb48 tr16 yHat (s * t) = emb48 tr16 yHat s * emb48 tr16 yHat t) ∧
    (∀ s ∈ allT5, ∀ t ∈ allT5, emb48 tr16 yHat s = emb48 tr16 yHat t → s = t) :=
  c51_emb tr16 yHat T0C _ (fun _ => (PkCV.ev_cOf _).symm) (PkCV.ev_cOf _).symm c51_hom0

private theorem c51_emb1 :
    (∀ s ∈ allT5, ∀ t ∈ allT5, emb48 tr1 yHat1 (s * t) = emb48 tr1 yHat1 s * emb48 tr1 yHat1 t) ∧
    (∀ s ∈ allT5, ∀ t ∈ allT5, emb48 tr1 yHat1 s = emb48 tr1 yHat1 t → s = t) :=
  c51_emb tr1 yHat1 T1C _ tr1_eq (PkCV.ev_cOf _).symm c51_hom1

private theorem emb48_mul0_chk_17 : allT5.all (fun s => allT5.all fun t =>
    decide (emb48 tr16 yHat (s * t) = emb48 tr16 yHat s * emb48 tr16 yHat t)) = true := by
  simp only [List.all_eq_true, decide_eq_true_eq]
  exact c51_emb0.1

private theorem emb48_mul1_chk_18 : allT5.all (fun s => allT5.all fun t =>
    decide (emb48 tr1 yHat1 (s * t) = emb48 tr1 yHat1 s * emb48 tr1 yHat1 t)) = true := by
  simp only [List.all_eq_true, decide_eq_true_eq]
  exact c51_emb1.1

private theorem emb48_inj0_chk_19 : allT5.all (fun s => allT5.all fun t =>
    imp (decide (emb48 tr16 yHat s = emb48 tr16 yHat t)) (decide (s = t))) = true := by
  simp only [List.all_eq_true]
  intro s hs t ht
  by_cases h : emb48 tr16 yHat s = emb48 tr16 yHat t
  · simp [imp, c51_emb0.2 s hs t ht h]
  · simp [imp, h]

private theorem emb48_inj1_chk_20 : allT5.all (fun s => allT5.all fun t =>
    imp (decide (emb48 tr1 yHat1 s = emb48 tr1 yHat1 t)) (decide (s = t))) = true := by
  simp only [List.all_eq_true]
  intro s hs t ht
  by_cases h : emb48 tr1 yHat1 s = emb48 tr1 yHat1 t
  · simp [imp, c51_emb1.2 s hs t ht h]
  · simp [imp, h]

private theorem RhatL0_mul_chk_36 : mulClosedChkP RhatL0 = true :=
  c51_mulTr tr16
    (c51_hyps tr16 yHat T0C _ (fun _ => (PkCV.ev_cOf _).symm) (PkCV.ev_cOf _).symm c51_hom0).1

private theorem RhatL1_mul_chk_38 : mulClosedChkP RhatL1 = true :=
  c51_mulTr tr1 (c51_hyps tr1 yHat1 T1C _ tr1_eq (PkCV.ev_cOf _).symm c51_hom1).1

private theorem emb48_mem0_chk_21 : allT5.all (fun t => decide (emb48 tr16 yHat t ∈ Sh0L)) = true := by
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro t ht
  obtain ⟨i, h | h⟩ := c51_emb_form tr16 yHat ht <;> rw [h] <;> unfold Sh0L <;>
    simp only [List.mem_flatMap, List.mem_map]
  · exact ⟨i, List.mem_finRange i, 1, List.mem_cons_self, mul_one _⟩
  · exact ⟨i, List.mem_finRange i, yHat, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩

private theorem emb48_mem1_chk_22 : allT5.all (fun t => decide (emb48 tr1 yHat1 t ∈ Sh1L)) = true := by
  simp only [List.all_eq_true, decide_eq_true_eq, sh1L_eq, mem_map_ev_iff]
  intro t ht
  obtain ⟨i, h | h⟩ := c51_emb_form tr1 yHat1 ht <;> rw [h]
  · exact sh1_chk.2.2.2.2.2.1 _ (List.mem_map_of_mem (List.mem_finRange i))
  · exact sh1_chk.2.2.2.2.1 i

end CertificateChecks.Batch5051

namespace Certificates

end Certificates
