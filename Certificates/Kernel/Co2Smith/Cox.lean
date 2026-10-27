module

public import Certificates.Kernel.Co2Smith.Mark
public import Certificates.Kernel.Co2Smith.CoxK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.SmallF2.Native

theorem mkT_get {j : Nat} (hj : j < 15) : glMkT[j]! = unpackR 22 (TP j) := by
  have h := tp_k
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨hs, h⟩ := h
  obtain ⟨hw, he⟩ := h j hj
  unfold glMkT
  rw [getElem!_pos _ j (by simp [hj]), Array.getElem_ofFn, glR_eq hw]
  exact (eq_unpack_of_eqK he).symm

theorem tab_get {a b : Nat} (ha : a < 15) (hb : b < 15) :
    tabK (TB 0) a b = (a != b && eqK (powK (mulV (TP a) (TP b)) 3) IDP) ∧
      tabK (TB 1) a b = commK (TP a) (TP b) := by
  have h := tab_k
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h a ha b hb

theorem relTab_get {a b : Nat} (ha : a < 15) (hb : b < 15) :
    (glMkRelTab[a]!)[b]! = tabK (TB 0) a b := by
  rw [(tab_get ha hb).1]
  unfold glMkRelTab
  rw [getElem!_pos _ a (by simp [ha]), Array.getElem_ofFn, getElem!_pos _ b (by simp [hb]),
    Array.getElem_ofFn]
  simp only
  rw [mkT_get ha, mkT_get hb, mulRows_unpack, powRows_unpack, idRows_eq, beq_unpack]

theorem comTab_get {a b : Nat} (ha : a < 15) (hb : b < 15) :
    (glMkComTab[a]!)[b]! = tabK (TB 1) a b := by
  rw [(tab_get ha hb).2]
  unfold glMkComTab
  rw [getElem!_pos _ a (by simp [ha]), Array.getElem_ofFn, getElem!_pos _ b (by simp [hb]),
    Array.getElem_ofFn]
  simp only
  rw [mkT_get ha, mkT_get hb, commRows_unpack]

theorem path_eq {a b c d e : Nat} (ha : a < 15) (hb : b < 15) (hc : c < 15) (hd : d < 15)
    (he : e < 15) :
    glMkPathOK glMkRelTab glMkComTab a b c d e = pathK (TB 0) (TB 1) a b c d e := by
  unfold glMkPathOK pathK
  rw [relTab_get ha hb, relTab_get hb hc, relTab_get hc hd, relTab_get hd he, comTab_get ha hc,
    comTab_get ha hd, comTab_get ha he, comTab_get hb hd, comTab_get hb he, comTab_get hc he]

theorem all_congr_mem {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem conjPath_eq (G : Nat) (p : List Nat) :
    glMkConjPath glMkT (unpackR 22 G) p = conjPathK TP G p := by
  unfold glMkConjPath conjPathK
  congr 1
  apply all_congr_mem
  intro i hi
  rw [List.mem_range] at hi
  by_cases hp : p[i]! < 15
  · rw [decide_eq_true hp, mkT_get (by omega), mkT_get hp, mulRows_unpack, mulRows_unpack,
      beq_unpack]
  · rw [decide_eq_false hp, Bool.false_and, Bool.false_and]

theorem cox_ok : glMkCoxOK = true := by
  have hC := coxConj_k
  have hL := coxLoop_k
  simp only [Bool.and_eq_true, List.all_eq_true] at hC
  obtain ⟨hP, hC⟩ := hC
  unfold coxLoopK at hL
  simp only [List.all_eq_true, List.mem_range] at hL
  unfold glMkCoxOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [path_eq (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hP
  · intro e he
    obtain ⟨⟨hw, hz⟩, hp⟩ := hC e he
    simp only [List.all_eq_true, decide_eq_true_eq] at hw
    rw [glR_eq hw, glZ_eq, commRows_unpack, conjPath_eq]
    exact ⟨hz, hp⟩
  · intro a ha b hb c hc d hd e he
    rw [path_eq ha hb hc hd he]
    exact hL a ha b hb c hc d hd e he

end CertificateChecks.KernelCo2Smith
