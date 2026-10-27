module

public import CFSG.Quasithin.AppendixH.H12.ModelM0
import CFSG.Quasithin.AppendixH.H12.ModelM0K
import CFSG.Quasithin.AppendixH.H12.ModelV2K
import CFSG.Quasithin.AppendixH.H12.ModelV2T0K

public section

namespace CFSG.Quasithin.AppendixH.H12.Model

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H12Cert
  CFSG.Quasithin.H13.MatNCert CFSG.Open
open CFSG.ASVolI.ChH (IsConjPt IsIsoPoint IsExtOf IsIntDirect cenIn ptStab)

private theorem list_two_valid {a b : ℕ} (ha : a < 4096) (hb : b < 4096) :
    ∀ c ∈ [a, b], c < 4096 := by
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption

private theorem tU_append (w w' : List ℕ) : tU (w ++ w') = tU w * tU w' := by
  simp only [tU, List.map_append, List.prod_append]

private theorem tU_nil : tU ([] : List ℕ) = 1 := by
  simp only [tU, List.map_nil, List.prod_nil]

private theorem eq_1465_of_mem_hypPts {r : ℕ} (hr : r ∈ hypPts) (h : ptSub r = ptSub 1465) :
    r = 1465 := by
  have hline : r ∈ lineOf 1465 :=
    (ptSub_eq_iff (by norm_num) (by norm_num) (hypPts_lt r hr)).mp h.symm
  have hcheck : hypPts.all (fun r => !((lineOf 1465).contains r) || (r == 1465)) = true := by
    decide +kernel
  have hc := (List.all_eq_true.mp hcheck) r hr
  rw [List.contains_iff_mem.mpr hline, Bool.not_true, Bool.false_or] at hc
  exact beq_iff_eq.mp hc

theorem ptSub_five_le_Wsub : ptSub 5 ≤ Wsub := by
  rw [ptSub, Wsub]
  refine (spanSub_le_iff (list_two_valid (by norm_num) (z12_lt 5)) Wb_valid).mpr ?_
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact List.contains_iff_mem.mp (by decide +kernel)
  · exact List.contains_iff_mem.mp (by decide +kernel)

theorem ptSub_1465_le_Wsub : ptSub 1465 ≤ Wsub := by
  rw [ptSub, Wsub]
  refine (spanSub_le_iff (list_two_valid (by norm_num) (z12_lt 1465)) Wb_valid).mpr ?_
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact List.contains_iff_mem.mp (by decide +kernel)
  · exact List.contains_iff_mem.mp (by decide +kernel)

theorem ptSub_five_ne_1465 : ptSub 5 ≠ ptSub 1465 := by
  intro h
  have hline : 1465 ∈ lineOf 5 :=
    (ptSub_eq_iff (by norm_num) (by norm_num) (by norm_num)).mp h
  exact absurd hline (by decide +kernel)

@[expose] def conjWords : List (ℕ × List ℕ) := [
    (5, []),
    (113, [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0]),
    (116, [1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0]),
    (123, [1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1]),
    (126, [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1]),
    (1313, [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1]),
    (1323, [1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1]),
    (1360, [1, 0, 1, 1, 1, 0]),
    (1375, [1, 0, 1, 1, 1]),
    (1459, [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1]),
    (1462, [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0]),
    (1474, [1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0]),
    (1479, [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1]),
    (1480, [1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1]),
    (1485, [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0]),
    (1316, [1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1]),
    (1326, [1, 0, 1, 1, 1]),
    (1365, [1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0]),
    (1370, [1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1]),
    (1465, []),
    (1468, [0])]

theorem conjWords_spec : ∀ rw ∈ conjWords, tU rw.2 ∈ M0 ∧
    (if rw.1 ∈ hypPts then mvN (tW rw.2) rw.1 ∈ lineOf 1465
      else mvN (tW rw.2) rw.1 ∈ lineOf 5) := by
  have h1 : conjWords.all
      (fun rw => Wb.all (fun c => (spanN Wb).contains (mvN (tW rw.2) c))) = true := by
    simp only [ModelM0K.contains_Wb_raw, ModelM0K.tW_eq]
    decide +kernel
  have h2 : conjWords.all (fun rw => decide
      (if rw.1 ∈ hypPts then mvN (tW rw.2) rw.1 ∈ lineOf 1465
        else mvN (tW rw.2) rw.1 ∈ lineOf 5)) = true := by
    simp only [ModelM0K.tW_eq]
    decide +kernel
  intro rw hrw
  refine ⟨?_, ?_⟩
  · refine (tU_mem_ptStab_spanSub_iff Wb_valid rw.2).mpr ?_
    intro c hc
    exact List.contains_iff_mem.mp ((List.all_eq_true.mp ((List.all_eq_true.mp h1) rw hrw)) c hc)
  · exact of_decide_eq_true ((List.all_eq_true.mp h2) rw hrw)

theorem conjWords_cover : ∀ r ∈ nonhypPts ++ hypPts, ∃ w, (r, w) ∈ conjWords := by
  have h : (nonhypPts ++ hypPts).all (fun r => conjWords.any (fun p => p.1 == r)) = true := by
    decide +kernel
  intro r hr
  obtain ⟨p, hp, hpr⟩ := List.any_eq_true.mp ((List.all_eq_true.mp h) r hr)
  exact ⟨p.2, by rw [← beq_iff_eq.mp hpr]; exact hp⟩

theorem isoPoint_conj_M0 {P : Subgroup Vec12} (hP : IsIsoPoint ι0 f0 P) (hPW : P ≤ Wsub) :
    IsConjPt glHom M0 P (ptSub 5) ∨ IsConjPt glHom M0 P (ptSub 1465) := by
  obtain ⟨c, hc0, hc, hq, rfl⟩ := (isIsoPoint_iff P).mp hP
  have hdcW : dc c ∈ Wsub := hPW (Subgroup.subset_closure ⟨c, List.mem_cons_self, rfl⟩)
  have hcW : c ∈ spanN Wb := (dc_mem_spanSub_iff Wb_valid hc).mp (by simpa [Wsub] using hdcW)
  have hc0' : c ≠ 0 := ne_of_gt hc0
  obtain hzero | ⟨r, hr, hcr⟩ := (mem_Wb_iff hc).mp hcW
  · exact absurd hzero hc0'
  · have hrpos : 0 < r := by
      have h : (nonhypPts ++ hypPts).all (fun r => decide (0 < r)) = true := by decide +kernel
      exact of_decide_eq_true ((List.all_eq_true.mp h) r hr)
    have hrlt : r < 4096 := by
      rcases List.mem_append.mp hr with h | h
      · exact nonhypPts_lt r h
      · exact hypPts_lt r h
    have hcd : ptSub c = ptSub r := (ptSub_eq_of_mem hrpos hrlt hcr).symm
    obtain ⟨w, hw⟩ := conjWords_cover r hr
    obtain ⟨hwM, hwpos⟩ := conjWords_spec (r, w) hw
    have hsmul : smulSub (tU w) (ptSub r) = ptSub (mvN (tW w) r) := by
      rw [smulSub_ptSub (M0_le_G0 hwM) hrlt, gmv_tU]
    by_cases hhyp : r ∈ hypPts
    · right
      have hline : mvN (tW w) r ∈ lineOf 1465 := by
        have := hwpos
        rwa [if_pos hhyp] at this
      rw [hcd]
      refine ⟨tU w, hwM, ?_⟩
      change smulSub (tU w) (ptSub r) = ptSub 1465
      rw [hsmul]
      exact (ptSub_eq_of_mem (by norm_num) (by norm_num) hline).symm
    · left
      have hline : mvN (tW w) r ∈ lineOf 5 := by
        have := hwpos
        rwa [if_neg hhyp] at this
      rw [hcd]
      refine ⟨tU w, hwM, ?_⟩
      change smulSub (tU w) (ptSub r) = ptSub 5
      rw [hsmul]
      exact (ptSub_eq_of_mem (by norm_num) (by norm_num) hline).symm

theorem not_isConjPt_M0_five_1465 : ¬ IsConjPt glHom M0 (ptSub 5) (ptSub 1465) := by
  intro h
  obtain ⟨g, hg, hgP⟩ := h
  exact not_isConjPt_five_1465 ⟨g, M0_le_G0 hg, hgP⟩

theorem ptStab_V2_le_M0 : ptStab glHom G0 (ptSub 1465) ≤ M0 := by
  intro g hg
  rw [mem_ptStab_iff] at hg ⊢
  obtain ⟨hgG, hgfix⟩ := hg
  refine ⟨hgG, ?_⟩
  obtain ⟨b', hb', hb'eq⟩ := planes_closed hgG Wb_mem_planes
  have hmemP : dc 1465 ∈ smulSub g (ptSub 1465) := by
    rw [hgfix]
    exact Subgroup.subset_closure ⟨1465, List.mem_cons_self, rfl⟩
  have hmem : dc 1465 ∈ spanSub b' := by
    rw [← hb'eq]
    exact Subgroup.map_mono (f := (glHom g).toMonoidHom) ptSub_1465_le_Wsub hmemP
  have h1465 : 1465 ∈ spanN b' :=
    (dc_mem_spanSub_iff (planes_valid b' hb') (by norm_num)).mp hmem
  have hb'W : spanSub b' = Wsub := plane_through_1465 hb' (by simp [lineOf]) h1465
  change smulSub g (spanSub Wb) = spanSub Wb
  rw [hb'eq]
  exact hb'W

theorem ptStab_M0_V2 : ptStab glHom M0 (ptSub 1465) = ptStab glHom G0 (ptSub 1465) := by
  apply le_antisymm
  · intro g hg
    rw [mem_ptStab_iff] at hg ⊢
    exact ⟨M0_le_G0 hg.1, hg.2⟩
  · intro g hg
    rw [mem_ptStab_iff]
    exact ⟨ptStab_V2_le_M0 hg, ((mem_ptStab_iff G0 (ptSub 1465) g).mp hg).2⟩

@[expose] def hyp5 : List ℕ := [1316, 1326, 1365, 1370, 1468]

@[expose] def hyp5Gen (i : ℕ) : List ℕ := [hyp5.getD i 0, mvN z12 (hyp5.getD i 0)]

private theorem hyp5_length : hyp5.length = 5 := by decide

theorem hyp5_sub : ∀ r ∈ hyp5, r ∈ hypPts := by
  have h : hyp5.all (fun r => hypPts.contains r) = true := by decide
  intro r hr
  exact List.contains_iff_mem.mp ((List.all_eq_true.mp h) r hr)

theorem hyp5_ne : ∀ r ∈ hyp5, r ≠ 1465 := by
  have h : hyp5.all (fun r => r != 1465) = true := by decide
  intro r hr
  exact bne_iff_ne.mp ((List.all_eq_true.mp h) r hr)

theorem hyp5Gen_valid : ∀ i < 5, ∀ c ∈ hyp5Gen i, c < 4096 := by
  have h : (List.range 5).all (fun i => (hyp5Gen i).all (fun c => decide (c < 4096))) = true := by
    decide +kernel
  intro i hi c hc
  exact of_decide_eq_true ((List.all_eq_true.mp ((List.all_eq_true.mp h) i (List.mem_range.mpr hi))) c hc)

theorem hyp5Gen_inj : ∀ i < 5, ∀ j < 5, spanSub (hyp5Gen i) = spanSub (hyp5Gen j) → i = j := by
  have hnd : ((List.range 5).map (fun i => spanMask (hyp5Gen i))).Nodup := by
    decide +kernel
  intro i hi j hj hij
  have hm : spanMask (hyp5Gen i) = spanMask (hyp5Gen j) :=
    (spanMask_eq_iff (hyp5Gen_valid i hi) (hyp5Gen_valid j hj)).mpr hij
  exact List.inj_on_of_nodup_map hnd (List.mem_range.mpr hi) (List.mem_range.mpr hj) hm

theorem vecStab_1465_le_M0 : vecStab 1465 ≤ M0 := by
  intro x hx
  obtain ⟨hxG, hxfix⟩ := (mem_vecStab_iff (by norm_num) x).mp hx
  have hmem : x ∈ ptStab glHom G0 (ptSub 1465) := by
    rw [mem_ptStab_iff]
    exact ⟨hxG, by rw [smulSub_ptSub hxG (by norm_num), hxfix]⟩
  exact ptStab_V2_le_M0 hmem

theorem Q0_le_vecStab_1465 : Q0 ≤ vecStab 1465 := by
  intro q hq
  obtain ⟨hqG, hqfix⟩ := (mem_cenIn_iff G0 Wsub q).mp hq
  rw [mem_vecStab_iff (by norm_num)]
  refine ⟨hqG, ?_⟩
  have h1 : glHom q (dc 1465) = dc 1465 :=
    hqfix (dc 1465) (ptSub_1465_le_Wsub (Subgroup.subset_closure ⟨1465, List.mem_cons_self, rfl⟩))
  rw [glHom_dc] at h1
  exact dc_inj (gmv_lt q 1465) (by norm_num) h1

theorem exists_p2 : ∃ π : ↥(vecStab 1465) →* Equiv.Perm (Fin 5),
    ∀ (g : ↥(vecStab 1465)) (i : Fin 5),
      smulSub (g : Γ12) (spanSub (hyp5Gen i)) = spanSub (hyp5Gen (π g i)) := by
  refine exists_actHom (vecStab 1465) hyp5Gen hyp5Gen_inj ?_
  intro g hg i hi
  set r := hyp5.getD i 0 with hrdef
  have hr5 : r ∈ hyp5 := by
    rw [hrdef]
    rw [List.getD_eq_getElem _ _ (by simpa [hyp5_length] using hi)]
    exact List.getElem_mem _
  have hrhyp : r ∈ hypPts := hyp5_sub r hr5
  have hrlt : r < 4096 := hypPts_lt r hrhyp
  have hgM : g ∈ M0 := vecStab_1465_le_M0 hg
  obtain ⟨r', hr', hconj⟩ := exists_hyp_image hgM hrhyp
  have hr'ne : r' ≠ 1465 := by
    intro heq
    have hgvec : gmv g 1465 = 1465 := (mem_vecStab_iff (by norm_num) g).mp hg |>.2
    have hfix : smulSub g (ptSub 1465) = ptSub 1465 := by
      rw [smulSub_ptSub (vecStab_le_G0 1465 hg) (by norm_num), hgvec]
    have hpr : ptSub r = ptSub 1465 := by
      have h1 : smulSub g (ptSub r) = smulSub g (ptSub 1465) := by
        rw [hconj, heq, hfix]
      have h2 := congrArg (smulSub g⁻¹) h1
      rwa [← smulSub_mul, inv_mul_cancel, smulSub_one, ← smulSub_mul, inv_mul_cancel,
        smulSub_one] at h2
    exact hyp5_ne r hr5 (eq_1465_of_mem_hypPts hrhyp hpr)
  have hr'5 : r' ∈ hyp5 := by
    have hcheck : hypPts.all (fun r => (r == 1465) || hyp5.contains r) = true := by
      decide +kernel
    have hh := (List.all_eq_true.mp hcheck) r' hr'
    rw [Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · exact absurd (beq_iff_eq.mp hh) hr'ne
    · exact List.contains_iff_mem.mp hh
  obtain ⟨j, hj, hjget⟩ := List.mem_iff_getElem.mp hr'5
  have hj5 : j < 5 := by rwa [hyp5_length] at hj
  refine ⟨j, hj5, ?_⟩
  have hspan_i : spanSub (hyp5Gen i) = ptSub r := by
    simp only [hyp5Gen, ← hrdef]
    rfl
  have hspan_j : spanSub (hyp5Gen j) = ptSub r' := by
    have hg' : hyp5.getD j 0 = r' := (List.getD_eq_getElem _ _ hj).trans hjget
    simp only [hyp5Gen, hg']
    rfl
  calc smulSub g (spanSub (hyp5Gen i)) = smulSub g (ptSub r) := by rw [hspan_i]
    _ = ptSub r' := hconj
    _ = spanSub (hyp5Gen j) := hspan_j.symm

noncomputable def p2 : ↥(vecStab 1465) →* Equiv.Perm (Fin 5) := Classical.choose exists_p2

theorem p2_spec (g : ↥(vecStab 1465)) (i : Fin 5) :
    smulSub (g : Γ12) (spanSub (hyp5Gen i)) = spanSub (hyp5Gen (p2 g i)) :=
  Classical.choose_spec exists_p2 g i

theorem p2_Q0 : ∀ q (hq : q ∈ Q0), p2 ⟨q, Q0_le_vecStab_1465 hq⟩ = 1 := by
  intro q hq
  refine actHom_eq_one p2 hyp5Gen hyp5Gen_inj p2_spec ⟨q, Q0_le_vecStab_1465 hq⟩ ?_
  intro i hi
  have hr5 : hyp5.getD i 0 ∈ hyp5 := by
    rw [List.getD_eq_getElem _ _ (by simpa [hyp5_length] using hi)]
    exact List.getElem_mem _
  have hrhyp : hyp5.getD i 0 ∈ hypPts := hyp5_sub _ hr5
  have hrlt : hyp5.getD i 0 < 4096 := hypPts_lt _ hrhyp
  have hrW : hyp5.getD i 0 ∈ spanN Wb := by
    have h : hypPts.all (fun r => (spanN Wb).contains r) = true := by decide +kernel
    exact List.contains_iff_mem.mp ((List.all_eq_true.mp h) _ hrhyp)
  obtain ⟨hqG, hqfix⟩ := (mem_cenIn_iff G0 Wsub q).mp hq
  have hfixr : glHom q (dc (hyp5.getD i 0)) = dc (hyp5.getD i 0) :=
    hqfix _ ((dc_mem_spanSub_iff Wb_valid hrlt).mpr hrW)
  have hgmv : gmv q (hyp5.getD i 0) = hyp5.getD i 0 := by
    apply dc_inj (gmv_lt q _) hrlt
    change dc (mvN (colsN ((q : Matrix (Fin 12) (Fin 12) (ZMod 2)))) (hyp5.getD i 0)) =
      dc (hyp5.getD i 0)
    rw [← glHom_dc]
    exact hfixr
  have hsmul : smulSub q (ptSub (hyp5.getD i 0)) = ptSub (hyp5.getD i 0) := by
    rw [smulSub_ptSub hqG hrlt, hgmv]
  show smulSub q (ptSub (hyp5.getD i 0)) = ptSub (hyp5.getD i 0)
  exact hsmul

@[expose] def x60 : List (List ℕ) := [
    [], [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1],
    [0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
    [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1],
    [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1],
    [1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0],
    [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1],
    [1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1],
    [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0],
    [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
    [1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0],
    [0, 1, 0, 1, 1, 1, 0], [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0],
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
    [1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1],
    [0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    [1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1],
    [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0],
    [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1],
    [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1],
    [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0],
    [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0],
    [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0],
    [1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1],
    [0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0],
    [1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0],
    [0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1],
    [1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1],
    [1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0],
    [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    [0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0],
    [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1],
    [1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1],
    [0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1],
    [0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0],
    [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0],
    [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1],
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0],
    [1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1],
    [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1],
    [1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1],
    [1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1],
    [0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0],
    [1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1],
    [0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1],
    [1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0],
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0],
    [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0],
    [1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1],
    [0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    [0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0],
    [0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0],
    [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1],
    [0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1],
    [0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0],
    [0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1],
    [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0],
    [1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1]]

theorem x60_length : x60.length = 60 := by
  decide

theorem tU_x60_mem : ∀ w ∈ x60, tU w ∈ vecStab 1465 := by
  have h : x60.all (fun w => (mvN (tW w) 1465 == 1465)) = true := by
    simp only [ModelM0K.tW_eq]
    decide +kernel
  intro w hw
  rw [tU_mem_vecStab_iff (by norm_num)]
  exact beq_iff_eq.mp ((List.all_eq_true.mp h) w hw)

set_option maxRecDepth 200000 in
theorem x60_sig_nodup : (x60.map (sigOf hyp5Gen 5)).Nodup :=
  ModelM0K.sig_nodup hyp5Gen 5 x60 (by decide +kernel)

theorem p2_range : 60 ≤ Nat.card p2.range := by
  have h := length_le_card_range_of_sig p2 hyp5Gen hyp5Gen_valid p2_spec x60 tU_x60_mem
    x60_sig_nodup
  rwa [x60_length] at h

set_option maxRecDepth 200000 in
theorem O1465_length : O1465.length = 1386 := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem O1465_nodup : O1465.Nodup :=
  ModelV2K.nodup_of_nodupMK (by decide +kernel)

theorem O1465_pos : ∀ x ∈ O1465, 0 < x := by
  have h : O1465.all (fun x => decide (0 < x)) = true := by decide +kernel
  intro x hx
  exact of_decide_eq_true ((List.all_eq_true.mp h) x hx)

theorem card_vecStab_1465_le : Nat.card (vecStab 1465) ≤ 960 := by
  have h := card_vecStab_mul_le (c := 1465) (by norm_num) (by norm_num) O1465_nodup O1465_pos
    (fun x hx => reach1465 hx)
  rw [O1465_length, H12Cert.card_G] at h
  omega

theorem structure_X2 :
    Nat.card Q0 = 16 ∧ IsPGroup 2 Q0 ∧ pCoreOf 2 (vecStab 1465) = Q0 ∧
      IsExtOf (vecStab 1465) (pCoreOf 2 (vecStab 1465)) ↥(alternatingGroup (Fin 5)) := by
  exact structure_A5 (X := vecStab 1465) (R := Q0) card_vecStab_1465_le Q0_le_vecStab_1465
    card_Q0_ge p2 p2_Q0 p2_range

@[expose] def t0Word : List ℕ :=
    [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1,
     0, 1, 0, 1, 0, 1, 1, 0]

theorem t0_in_Q0 : tU t0Word ∈ Q0 := by
  refine (tU_mem_cenIn_spanSub_iff Wb_valid t0Word).mpr ?_
  have h : Wb.all (fun c => (mvN (tW t0Word) c == c)) = true := by decide +kernel
  intro c hc
  exact beq_iff_eq.mp ((List.all_eq_true.mp h) c hc)

theorem t0_orderOf : orderOf (tU t0Word) = 2 := by
  have ht2 : tU t0Word ^ 2 = 1 := by
    rw [pow_two, ← tU_append]
    have h : tW (t0Word ++ t0Word) = tW [] := by decide +kernel
    rw [tU_eq_of_tW_eq h, tU_nil]
  refine orderOf_eq_prime ht2 ?_
  intro h1
  have hne : tW t0Word ≠ tW [] := by decide +kernel
  apply hne
  have h2 := congrArg (fun u : Γ12 => colsN ((u : Matrix (Fin 12) (Fin 12) (ZMod 2)))) h1
  rw [colsN_tU, Units.val_one, colsN_one] at h2
  rw [show tW ([] : List ℕ) = oneN 12 from rfl]
  exact h2

theorem commV_t0 : commV (Subgroup.zpowers (glHom (tU t0Word))) = ptSub 5 ⊔ ptSub 1465 := by
  have hmap : commV (Subgroup.zpowers (glHom (tU t0Word))) =
      commV ((Subgroup.zpowers (tU t0Word)).map glHom) :=
    congrArg commV (MonoidHom.map_zpowers glHom (tU t0Word)).symm
  rw [hmap]
  have ht2 : (tU t0Word) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (tU t0Word)
    rwa [t0_orderOf] at this
  have hb : ∀ c ∈ [5, mvN z12 5, 1465, mvN z12 1465], c < 4096 := by
    intro c hc
    have h : ([5, mvN z12 5, 1465, mvN z12 1465]).all (fun c => decide (c < 4096)) = true := by
      decide +kernel
    exact of_decide_eq_true ((List.all_eq_true.mp h) c hc)
  have hle : ∀ g ∈ Subgroup.zpowers (tU t0Word), ∀ c < 4096,
      gmv g c ^^^ c ∈ spanN [5, mvN z12 5, 1465, mvN z12 1465] := by
    intro g hg c hc
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [← hk]
    have hkmod : (tU t0Word) ^ k = (tU t0Word) ^ (k % 2) :=
      zpow_eq_zpow_emod k (by rw [zpow_ofNat]; exact ht2)
    rw [hkmod]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [h0, zpow_zero, gmv_one hc, Nat.xor_self]
      exact List.contains_iff_mem.mp (by decide +kernel)
    · rw [h1, zpow_one, gmv_tU]
      have hall : (List.range 4096).all
          (fun c => (spanN [5, mvN z12 5, 1465, mvN z12 1465]).contains
            (mvN (tW t0Word) c ^^^ c)) = true := by
        rw [ModelV2T0K.all_comm_eq]
        decide +kernel
      exact List.contains_iff_mem.mp ((List.all_eq_true.mp hall) c (List.mem_range.mpr hc))
  have hge : ∀ x ∈ [5, mvN z12 5, 1465, mvN z12 1465],
      ∃ g ∈ Subgroup.zpowers (tU t0Word), ∃ c < 4096, gmv g c ^^^ c = x := by
    intro x hx
    have hany : ([5, mvN z12 5, 1465, mvN z12 1465]).all
        (fun x => (List.range 4096).any (fun c => (mvN (tW t0Word) c ^^^ c) == x)) = true := by
      rw [ModelV2T0K.all_any_comm_eq]
      decide +kernel
    obtain ⟨c, hc, hcx⟩ := List.any_eq_true.mp ((List.all_eq_true.mp hany) x hx)
    exact ⟨tU t0Word, Subgroup.mem_zpowers (tU t0Word), c, List.mem_range.mp hc, by
      rw [gmv_tU]; exact beq_iff_eq.mp hcx⟩
  have hcomm := commV_map_eq_spanSub (X := Subgroup.zpowers (tU t0Word))
    (b := [5, mvN z12 5, 1465, mvN z12 1465]) hb hle hge
  rw [hcomm]
  exact (spanSub_append [5, mvN z12 5] [1465, mvN z12 1465]).symm

theorem exists_t0 :
    ∃ t ∈ pCoreOf 2 M0, orderOf t = 2 ∧
      commV (Subgroup.zpowers (glHom t)) = ptSub 5 ⊔ ptSub 1465 := by
  refine ⟨tU t0Word, ?_, t0_orderOf, commV_t0⟩
  rw [structure_M0.2.1]
  exact t0_in_Q0

theorem clause78_M0
    (hZ : (Subgroup.center ↥G0).map G0.subtype = Subgroup.zpowers zU) :
    Clause78 glHom G0 M0 ι0 f0 (ptSub 5) (ptSub 1465) := by
  unfold Clause78
  rw [structure_M0.2.1, fixV_Q0]
  refine ⟨isIsoPoint_1465, ptSub_five_le_Wsub, ptSub_1465_le_Wsub, ptSub_five_ne_1465, ?_,
    not_isConjPt_M0_five_1465, ptStab_M0_V2, ?_, ?_, not_isConjPt_five_1465, ?_⟩
  · intro P hP hPW
    exact isoPoint_conj_M0 hP hPW
  · refine ⟨vecStab 1465, ?_, ?_, ?_, ?_⟩
    · rw [hZ]
      exact isIntDirect_ptStab (c := 1465) (by norm_num) (by norm_num)
    · rw [structure_X2.2.2.1]
      exact Q0_isElemAbelian
    · rw [structure_X2.2.2.1]
      exact structure_X2.1
    · exact structure_X2.2.2.2
  · intro P hP
    exact isoPoint_conj hP
  · rw [← structure_M0.2.1]
    exact exists_t0

end CFSG.Quasithin.AppendixH.H12.Model
