module

public import Certificates.Kernel.A312M23.Checks
public import Certificates.Kernel.M23Dc.Bridge
public import CFSG.Certificates.Kernel.A312M23KSound
public import CFSG.Quasithin.Background.HSporLatM23Sg
public import CFSG.LieType.Multipliers.L34Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender

set_option maxRecDepth 100000

public section

namespace CFSG.KD.A312M23

open CFSG.KC.A312M23K CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H.MathieuLat
open CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Sporadic.Schreier (m23GenA m23GenB)

@[expose] noncomputable def abE (i : ℕ) : CFSG.KD.M23Dc.G := [m23GenA, m23GenB].getD i 1

@[expose] noncomputable def sgE (i : ℕ) : CFSG.KD.M23Dc.G :=
  [CFSG.KD.M23Dc.E 167, CFSG.KD.M23Dc.E 188, CFSG.KD.M23Dc.E 197].getD i 1

theorem mw_eq : CFSG.KD.M23Dc.J.mw.toArray = CFSG.Quasithin.A312M23.m23MwLit := by
  apply eq_of_beq
  quickRfl

theorem y1GA_eq : y1GA = CFSG.Quasithin.A312M23.m22TabA.toList := by
  apply eq_of_beq
  quickRfl

theorem y1GB_eq : y1GB = CFSG.Quasithin.A312M23.m22TabB.toList := by
  apply eq_of_beq
  quickRfl

theorem y2Rel_eq : y2Rel = CFSG.LieType.Multipliers.L34.rels.map
    (List.map fun l => bif l.2 then l.1.val else l.1.val + 2) := by
  have e : CFSG.LieType.Multipliers.L34.rels.map
      (List.map fun l => bif l.2 then l.1.val else l.1.val + 2) =
      [[0, 0], [1, 1, 1, 1, 1], [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
        [0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3],
        [0, 1, 1, 2, 3, 3, 0, 1, 1, 2, 3, 3, 0, 1, 1, 2, 3, 3],
        [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1],
        [0, 1, 0, 1, 1, 0, 3, 0, 1, 0, 1, 1, 0, 3, 0, 1, 0, 1, 1, 0, 3, 0, 1, 0, 1, 1, 0, 3,
          0, 1, 0, 1, 1, 0, 3, 0, 1, 0, 1, 1, 0, 3, 0, 1, 0, 1, 1, 0, 3]] := by
    simp [CFSG.LieType.Multipliers.L34.rels, CFSG.LieType.Multipliers.L34.parseWord]
  rw [e]
  apply eq_of_beq
  quickRfl

theorem rep_tabs {l : ℕ} (hl : l < 8) :
    Rep 23 CFSG.KD.M23Dc.J.tabs l ((m23GenA :: m23GenB :: CFSG.KD.M23Dc.sl).getD l 1) := by
  intro p _
  have h : tab 23 ((m23GenA :: m23GenB :: CFSG.KD.M23Dc.sl).getD l 1) =
      CFSG.KD.M23Dc.J.tabs.getD l [] := by
    simpa using congrArg Array.toList (CFSG.KD.M23Dc.tab_letter hl)
  unfold tf act
  rw [h]

theorem rep_AB : ∀ i < AB.length, Rep 23 AB i (abE i) := by
  intro i hi
  have hAB : AB.length = 2 := by simp [AB, CFSG.KD.M23Dc.tabs_eq]
  rw [hAB] at hi
  intro p hp
  have e := rep_tabs (l := i) (by omega) p hp
  have e1 : tf AB i p = tf CFSG.KD.M23Dc.J.tabs i p := by
    simp [tf, AB, List.getD_eq_getElem?_getD, List.getElem?_take, hi]
  have e2 : (m23GenA :: m23GenB :: CFSG.KD.M23Dc.sl).getD i 1 = abE i := by
    interval_cases i <;> rfl
  rw [e1, e, e2]

theorem m23Sg_eq : m23Sg = [sgE 0, sgE 1, sgE 2] := by
  have h := CFSG.KD.M23Dc.m23Sg_eq
  simp only [CFSG.KD.M23Dc.m23Sg, m23Qp, List.map_cons, List.map_nil] at h
  simp only [m23Sg, m23Qp, List.map_cons, List.map_nil]
  change _ = [CFSG.KD.M23Dc.E 167, CFSG.KD.M23Dc.E 188, CFSG.KD.M23Dc.E 197]
  exact h

theorem rep_Sg : ∀ i < Sg.length, Rep 23 Sg i (sgE i) := by
  intro i hi
  have hS : Sg.length = 3 := by
    rw [Sg, CFSG.KD.M23Dc.tabs_eq]
    rfl
  rw [hS] at hi
  intro p hp
  have e := rep_tabs (l := 2 + i) (by omega) p hp
  have e1 : tf Sg i p = tf CFSG.KD.M23Dc.J.tabs (2 + i) p := by
    simp only [tf, Sg, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
      if_pos hi]
  have e2 : (m23GenA :: m23GenB :: CFSG.KD.M23Dc.sl).getD (2 + i) 1 = sgE i := by
    interval_cases i <;> simp [CFSG.KD.M23Dc.sl, sgE]
  rw [e1, e, e2]

theorem gw_eq {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ 9) :
    gw j = CFSG.Quasithin.A312M23.m23MwLit[j]! := by
  have e : CFSG.KD.M23Dc.J.mw.getD j [] = CFSG.Quasithin.A312M23.m23MwLit[j]! := by
    rw [← mw_eq]
    simp [List.getD_eq_getElem?_getD]
    rfl
  rw [gw, e]
  interval_cases j <;> rfl

theorem YT_eq {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ 9) {T : List (List ℕ)}
    (hel : ∀ l < Sg.length + (gw j).length, el CFSG.KD.M23Dc.G 23 T l =
      letE Sg (gw j) sgE abE l) :
    YT CFSG.KD.M23Dc.G 23 T (Sg.length + (gw j).length) = m23Member j := by
  have hS : Sg.length = 3 := by simp [Sg, CFSG.KD.M23Dc.tabs_eq]
  have hg := gw_eq hj1 hj
  obtain ⟨w, hw⟩ : ∃ w, gw j = [w] := ⟨_, rfl⟩
  rw [hg] at hw
  rw [YT, m23Member, hw]
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, List.mem_append, List.mem_map, List.mem_singleton]
  have hgl : (gw j).length = 1 := by rw [hg, hw]; rfl
  rw [hgl, hS]
  have hsg : m23Sg = [sgE 0, sgE 1, sgE 2] := m23Sg_eq
  have h3 : letE Sg (gw j) sgE abE 3 = wordElt m23GenA m23GenB w := by
    rw [letE, if_neg (by omega), hS, hg, hw]
    simp only [Nat.sub_self, List.getD_cons_zero, wordElt, evalElt]
    congr 1
    refine List.map_congr_left fun a _ => ?_
    simp [abE, List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]
  constructor
  · rintro ⟨l, hl, rfl⟩
    rw [hel l (by omega)]
    rcases (by omega : l < 3 ∨ l = 3) with h | rfl
    · left
      rw [letE, if_pos (by omega), hsg]
      interval_cases l <;> simp
    · right
      exact ⟨w, rfl, h3.symm⟩
  · rintro (h | ⟨w', rfl, rfl⟩)
    · rw [hsg] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl
      · exact ⟨0, by omega, by rw [hel 0 (by omega), letE, if_pos (by omega)]⟩
      · exact ⟨1, by omega, by rw [hel 1 (by omega), letE, if_pos (by omega)]⟩
      · exact ⟨2, by omega, by rw [hel 2 (by omega), letE, if_pos (by omega)]⟩
    · exact ⟨3, by omega, by rw [hel 3 (by omega), h3]⟩

end CFSG.KD.A312M23

end
