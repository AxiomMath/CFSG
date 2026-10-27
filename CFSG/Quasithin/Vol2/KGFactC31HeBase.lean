
module

public import CFSG.Sporadic.HeldB.BaseTests
public import CFSG.Sporadic.HeldB.OuterArith
public import CFSG.Quasithin.Vol2.KGFactC31HeElt
public import CFSG.Sporadic.HeldB.InnerRestrict

public section

namespace CFSG.Quasithin.KGC31.He

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB CFSG.Certificates
  CFSG.Certificates.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
  CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native _root_.Certificates

@[expose] noncomputable def gens2 : List (Equiv.Perm (Fin 8330)) := [heGenPerm 0, heGenPerm 1]

theorem rep_gA :
    ∀ h < gens3.length, Rep 8330 gA[h]! (gens3.getD h 1) := by
  intro h hh
  have hh3 : h < 3 := hh
  rw [gA, gens3]
  interval_cases h
  · rw [arr3_get0, list3_getD0]
    exact rep_heGen (by norm_num)
  · rw [arr3_get1, list3_getD1]
    exact rep_heGen (by norm_num)
  · rw [arr3_get2, list3_getD2]
    exact rep_heU

theorem rep_gAi :
    ∀ h < gens3.length, Rep 8330 gAi[h]! (gens3.getD h 1)⁻¹ := by
  intro h hh
  have hh3 : h < 3 := hh
  rw [gAi, map_getElem! _ _ (by simp [gA]; omega)]
  exact rep_invCand_of_rep (rep_gA h hh)

theorem rep_wA {w : List ℤ} (hw : lettersOK 3 w = true) :
    Rep 8330 (wA w) (elt w) :=
  rep_wordA_evalSignedWord rep_gA rep_gAi hw

theorem rep_wAi {w : List ℤ} (hw : lettersOK 3 w = true) :
    Rep 8330 (wAi w) (elt w)⁻¹ :=
  rep_invCand_of_rep (rep_wA hw)

theorem heAutU_mem' : heAutU ∈ heAutGroup := heAutU_mem_heAutGroup

theorem elt_mem_heAutGroup (w : List ℤ) : elt w ∈ heAutGroup :=
  evalSignedWord_mem heAutGroup (fun g hg => by
    simp only [gens3, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact heP_le_heAutGroup (heGenPerm_mem (by norm_num))
    · exact heP_le_heAutGroup (heGenPerm_mem (by norm_num))
    · exact heAutU_mem_heAutGroup) w

theorem lettersOK_mono {j k : ℕ} (hjk : j ≤ k) {w : List ℤ} (h : lettersOK j w = true) :
    lettersOK k w = true := by
  simp only [lettersOK, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h ⊢
  exact fun l hl => ⟨(h l hl).1, (h l hl).2.trans hjk⟩

theorem elt_eq_two {w : List ℤ} (hw : lettersOK 2 w = true) :
    elt w = evalSignedWord gens2 w :=
  (rep_wA (lettersOK_mono (by norm_num) hw)).unique
    (rep_wordA_evalSignedWord (gs := gens2) (S := gA) (Sinv := gAi)
      (fun h hh => by
        have := rep_gA h (by simp [gens2, gens3] at hh ⊢; omega)
        have h2 : h < 2 := by simpa [gens2] using hh
        interval_cases h <;> exact this)
      (fun h hh => by
        have := rep_gAi h (by simp [gens2, gens3] at hh ⊢; omega)
        have h2 : h < 2 := by simpa [gens2] using hh
        interval_cases h <;> exact this) hw)

theorem elt_mem_heP {w : List ℤ} (hw : lettersOK 2 w = true) :
    elt w ∈ heP := by
  rw [elt_eq_two hw]
  exact evalSignedWord_mem heP (fun g hg => by
    simp only [gens2, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact heGenPerm_mem (by norm_num)
    · exact heGenPerm_mem (by norm_num)) w

theorem lettersOK_append {j : ℕ} {a b : List ℤ} (ha : lettersOK j a = true)
    (hb : lettersOK j b = true) : lettersOK j (a ++ b) = true := by
  simp only [lettersOK, List.all_append, Bool.and_eq_true] at ha hb ⊢
  exact ⟨ha, hb⟩

theorem lettersOK_invW {j : ℕ} {w : List ℤ} (hw : lettersOK j w = true) :
    lettersOK j (invW w) = true := by
  simp only [lettersOK, invW, List.all_reverse, List.all_map, List.all_eq_true,
    Function.comp_apply, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hw ⊢
  intro l hl
  obtain ⟨h1, h2⟩ := hw l hl
  exact ⟨by omega, by rw [Int.natAbs_neg]; exact h2⟩

theorem elt_append {a b : List ℤ} (ha : lettersOK 3 a = true) (hb : lettersOK 3 b = true) :
    elt (a ++ b) = elt a * elt b := by
  have hab := lettersOK_append ha hb
  unfold elt
  rw [evalSignedWord, ite_eq_left (show lettersOK gens3.length (a ++ b) = true from hab),
    evalSignedWord, ite_eq_left (show lettersOK gens3.length a = true from ha),
    evalSignedWord, ite_eq_left (show lettersOK gens3.length b = true from hb)]
  simp only [toLetters, List.filterMap_append, Quiver.SchreierGraph.evalWord_append]

theorem elt_neg_single {l : ℤ} (hl : lettersOK 3 [l] = true) : elt [-l] = (elt [l])⁻¹ := by
  have hl' : lettersOK 3 [-l] = true := lettersOK_invW hl
  simp only [lettersOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, bne_iff_ne,
    ne_eq, decide_eq_true_eq] at hl
  unfold elt
  rw [evalSignedWord, ite_eq_left (show lettersOK gens3.length [-l] = true from hl'),
    evalSignedWord, ite_eq_left (show lettersOK gens3.length [l] = true by
      simp only [lettersOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
        bne_iff_ne, ne_eq, decide_eq_true_eq]
      exact hl)]
  rcases lt_or_gt_of_ne hl.1 with hneg | hpos
  · have h1 : ¬ 0 < l := by omega
    simp [toLetters, hl.1, hl.2, h1, hneg, gens3]
  · have h1 : ¬ l < 0 := by omega
    simp [toLetters, hl.1, hl.2, h1, hpos, gens3]

theorem elt_nil : elt [] = 1 := by
  unfold elt
  rw [evalSignedWord]
  split_ifs <;> simp [toLetters]

theorem elt_invW : ∀ {w : List ℤ}, lettersOK 3 w = true → elt (invW w) = (elt w)⁻¹
  | [], _ => by rw [show invW [] = [] from rfl, elt_nil, inv_one]
  | l :: w, hw => by
    have hl : lettersOK 3 [l] = true := by
      simp only [lettersOK, List.all_cons, List.all_nil, Bool.and_true] at hw ⊢
      exact (Bool.and_eq_true _ _).mp hw |>.1
    have hw' : lettersOK 3 w = true := by
      simp only [lettersOK, List.all_cons, Bool.and_eq_true] at hw ⊢
      exact hw.2
    have hinv : invW (l :: w) = invW w ++ [-l] := by simp [invW]
    rw [hinv, elt_append (b := [-l]) (lettersOK_invW hw') (lettersOK_invW hl), elt_invW hw',
      elt_neg_single hl, show l :: w = [l] ++ w from rfl, elt_append hl hw', mul_inv_rev]

theorem elt_conjW {n y : List ℤ} (hn : lettersOK 3 n = true) (hy : lettersOK 3 y = true) :
    elt (n ++ y ++ invW n) = elt n * elt y * (elt n)⁻¹ := by
  rw [elt_append (lettersOK_append hn hy) (lettersOK_invW hn), elt_append hn hy, elt_invW hn]

theorem bs_eq : bs = heBase := rfl

theorem hbs : ∀ b ∈ bs, b < 8330 := by decide

theorem baseFaithful_heP : BaseFaithful heP bs := heP_baseFaithful

theorem t1W_eq : t1W = heT1Word := by decide

theorem rep_t1A : Rep 8330 t1A heT1P := by
  have h := rep_wordA_evalSignedWord (gs := gens2) (S := gA) (Sinv := gAi)
    (w := heT1Word)
    (fun h hh => by
      have := rep_gA h (by simp [gens2, gens3] at hh ⊢; omega)
      have h2 : h < 2 := by simpa [gens2] using hh
      interval_cases h <;> exact this)
    (fun h hh => by
      have := rep_gAi h (by simp [gens2, gens3] at hh ⊢; omega)
      have h2 : h < 2 := by simpa [gens2] using hh
      interval_cases h <;> exact this) (by decide)
  rw [t1A, t1W_eq]
  rw [heT1P]
  exact h

theorem getElem!_wA_toArray (W : List (List ℤ)) {i : ℕ} (hi : i < W.length) :
    (W.map wA).toArray[i]! = wA (W.getD i []) := by
  rw [getElem!_pos _ i (by simpa using hi), List.getD_eq_getElem _ _ hi]
  simp

end CFSG.Quasithin.KGC31.He

end
