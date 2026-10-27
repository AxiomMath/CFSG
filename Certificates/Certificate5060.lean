module

public import CFSG.GH74.GLS.C3.Layer2.L5C3bInputs
import CFSG.Certificates.Kernel.L5.S0Words
import Certificates.Kernel.L5.S0Checks
import Mathlib.Algebra.Order.Ring.Star
import Std.Tactic.BVDecide.Normalize.Bool

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open CFSG.Certificates.Kernel CFSG.Certificates.Kernel.PkCV CFSG.KD.L5 CFSG.KD.L5.S0Checks
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5060

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open CFSG.Certificates.Kernel CFSG.Certificates.Kernel.PkCV CFSG.KD.L5 CFSG.KD.L5.S0Checks
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

private theorem tr1_eq (v : Fin 16) : tr1 v = ev (trC v) := by
  rw [trC, ← getD_map_ev, map_cOf_ev]
  rfl

private theorem ovC_eq (s : CV 16) : overV4 tr1 (ev s) = ovC s := by
  unfold overV4 rhoF ovC
  simp only [tr1_eq, ev_inv', ev_mul', decide_ev_eq']

private theorem S0L1_eq : S0L1 = SC.map ev := by
  have e3 : Sh1L = (closureList (sh1Gens.map cOf) 12).map ev := by
    rw [← closureList_map_ev, map_cOf_ev]
    rfl
  rw [S0L1, e3, List.filter_map, SC]
  exact congrArg (List.map ev) (List.filter_congr fun s _ => ovC_eq s)

private theorem gensS0_eq : gensS0 = gC.map ev := by
  rw [gensS0, map_nrm, gC, map_cOf_ev]

private theorem tabS0_eq : tabS0 = tabC.map evP := by
  rw [tabS0, gensS0_eq, wBfsTab_map_ev]
  rfl

private theorem entry {w : List ℕ} (hw : w ∈ tabC.map Prod.snd) : (ev (wval gC w), w) ∈ tabS0 := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw
  have hA' := List.all_eq_true.1 hA x hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hA'
  rw [tabS0_eq, hA'.1]
  exact List.mem_map.2 ⟨x, hx, rfl⟩

private theorem getD_lt {a b a' b' : CV 16} {i : ℕ} (hi : i < 4) :
    (fixC ++ [a, b]).getD i 1 = (fixC ++ [a', b']).getD i 1 := by
  have hl : fixC.length = 4 := by simp [fixC]
  rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]

private theorem getD_four (a b b' : CV 16) : (fixC ++ [a, b]).getD 4 1 = (fixC ++ [a, b']).getD 4 1 := rfl

private theorem getD_five (a a' b : CV 16) : (fixC ++ [a, b]).getD 5 1 = (fixC ++ [a', b]).getD 5 1 := rfl

private theorem holds_t1 (a b : CV 16) : holdsC (fixC ++ [a, b]) t1 = holdsC (fixC ++ [a, 1]) t1 := by
  unfold holdsC t1
  simp only
  rw [wval_eq_of_getD (w := [4, 1]) (L := fixC ++ [a, b]) (L' := fixC ++ [a, 1]),
    wval_eq_of_getD (w := [4]) (L := fixC ++ [a, b]) (L' := fixC ++ [a, 1]),
    wval_eq_of_getD (w := [1, 2]) (L := fixC ++ [a, b]) (L' := fixC ++ [a, 1])] <;>
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> first | exact getD_four _ _ _ | exact getD_lt (by norm_num)

private theorem holds_t2 (a b : CV 16) : holdsC (fixC ++ [a, b]) t2 = holdsC (fixC ++ [1, b]) t2 := by
  unfold holdsC t2
  simp only
  rw [wval_eq_of_getD (w := [5]) (L := fixC ++ [a, b]) (L' := fixC ++ [1, b]),
    wval_eq_of_getD (w := [1, 5]) (L := fixC ++ [a, b]) (L' := fixC ++ [1, b]),
    wval_eq_of_getD (w := [1, 3]) (L := fixC ++ [a, b]) (L' := fixC ++ [1, b])] <;>
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> first | exact getD_five _ _ _ | exact getD_lt (by norm_num)

private theorem fails {c₁ c₂ : CV 16} (hc₁ : c₁ ∈ SC) (hc₂ : c₂ ∈ SC) :
    ∃ t ∈ [t1, t2, t3], holdsC (fixC ++ [c₁, c₂]) t = false := by
  by_cases ha : holdsC (fixC ++ [c₁, 1]) t1 = true
  · by_cases hb : holdsC (fixC ++ [1, c₂]) t2 = true
    · refine ⟨t3, by simp, ?_⟩
      have h := List.all_eq_true.1 (List.all_eq_true.1 hD c₁ (List.mem_filter.2 ⟨hc₁, ha⟩)) c₂
        (List.mem_filter.2 ⟨hc₂, hb⟩)
      simpa using h
    · refine ⟨t2, by simp, ?_⟩
      rw [holds_t2]
      simpa using hb
  · refine ⟨t1, by simp, ?_⟩
    rw [holds_t1]
    simpa using ha

private theorem noCHatChk_true_0 : noCHatChk S0L1 = true := by
  unfold noCHatChk
  simp only [map_nrm, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro e he
    rw [tabS0_eq] at he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
    have hA' := List.all_eq_true.1 hA x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hA' ⊢
    rw [gensS0_eq, S0L1_eq, evP, wval_map_ev, hA'.1]
    exact ⟨rfl, List.mem_map_of_mem hA'.2⟩
  · rw [List.all_eq_true]
    intro s hs
    rw [S0L1_eq] at hs
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hs
    obtain ⟨x, hx, hxc⟩ := List.any_eq_true.1 (List.all_eq_true.1 hB c hc)
    rw [List.any_eq_true, tabS0_eq]
    refine ⟨evP x, List.mem_map_of_mem hx, ?_⟩
    simp only [decide_eq_true_eq] at hxc
    rw [beq_iff_eq, evP, hxc]
  · rw [List.all_eq_true]
    intro g hg
    rw [gensS0_eq] at hg
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hg
    have hC' := List.all_eq_true.1 hC c hc
    simp only [decide_eq_true_eq] at hC' ⊢
    rw [S0L1_eq]
    exact List.mem_map_of_mem hC'
  · rw [List.all_eq_true]
    intro u₁ hu₁
    rw [List.all_eq_true]
    intro u₂ hu₂
    rw [S0L1_eq] at hu₁ hu₂
    obtain ⟨c₁, hc₁, rfl⟩ := List.mem_map.1 hu₁
    obtain ⟨c₂, hc₂, rfl⟩ := List.mem_map.1 hu₂
    obtain ⟨t, ht, hne⟩ := fails hc₁ hc₂
    have hw := List.all_eq_true.1 hW t ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, hr⟩ := hw
    unfold holdsC at hr hne
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hr hne
    have himg : [tr1 (cHat 1), tr1 (cHat 2), tr1 (cHat 4), tr1 (cHat 8), ev c₁, ev c₂] =
        (fixC ++ [c₁, c₂]).map ev := by
      simp only [fixC, List.map_append, map_cOf_ev]
      rfl
    have hfst : (tabC.map evP).map Prod.fst = (tabC.map Prod.fst).map ev := by
      simp [evP, Function.comp_def]
    have hnd : (tabS0.map Prod.fst).Nodup := by
      rw [tabS0_eq, hfst, nodup_map_ev]
      exact hN
    rw [Bool.not_eq_true']
    refine homTab_eq_false hnd (entry h1) (entry h2) (entry h3) ?_ ?_
    · rw [hr]
      exact ev_mul _ _
    · rw [himg, wval_map_ev, wval_map_ev, wval_map_ev, ← ev_mul, Ne, ev_eq_iff]
      exact hne

end CertificateChecks.Batch5060

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5060 : noCHatChk S0L1 = true := by
  exact CertificateChecks.Batch5060.noCHatChk_true_0

end Certificates
