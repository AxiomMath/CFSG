module

public import CFSG.Sporadic.HNSchreier.AltCent
public import CFSG.Sporadic.HNSchreier.ThreeCheck
public import CFSG.Sporadic.HNSchreier.RankCheck
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2109

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Blueprint.NativeSporadic CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.He.Native Matrix

theorem evalWord_ptoLetters_eq {G : Type*} [Group G] (g : ℕ → G) {j : ℕ} (w : List ℤ)
    (hw : plettersOK j w = true) :
    Quiver.SchreierGraph.evalWord (fun h : Fin j => g h) (ptoLetters j w) =
      (w.map fun l => if 0 < l then g (l.natAbs - 1) else (g (l.natAbs - 1))⁻¹).prod := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [plettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : plettersOK j w = true := by
      simpa [plettersOK, List.all_eq_true] using hw
    have hcons : ptoLetters j (l :: w) = (⟨l.natAbs - 1, by omega⟩, decide (0 < l)) ::
        ptoLetters j w := by
      simp [ptoLetters, hl0, hlj]
    rw [hcons, List.map_cons, List.prod_cons, ← ih hw']
    by_cases hpos : 0 < l
    · rw [decide_eq_true hpos, Quiver.SchreierGraph.evalWord_cons_true, ite_eq_left hpos]
    · rw [show decide (0 < l) = false by simpa using hpos,
        Quiver.SchreierGraph.evalWord_cons_false, ite_eq_right hpos]

theorem permJ_hWordJ (w : List ℤ) : permJ (hWordJ w) =
    (w.map fun l => if 0 < l then hPerm (l.natAbs - 1) else (hPerm (l.natAbs - 1))⁻¹).prod := by
  rw [hWordJ, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_apply]
  split_ifs
  · exact permJ_hJ _
  · rw [map_inv, permJ_hJ]

theorem hStrongInv_rep :
    ∀ j < 17, PRep hnsData.n (pinvs hnsData.n hStrongArr)[j]! (hPerm j)⁻¹ := by
  intro j hj
  refine prep_inv_of_pisInv (hStrong_rep j hj) ?_
  have h1 := local_parts.1
  unfold strongOK at h1
  simp only [Bool.and_eq_true] at h1
  exact allBelowN_spec h1.1.2 (show j < hStrongArr.size by
    obtain ⟨-, hr⟩ := regs_rep
    have := (prep_of_strongOK local_parts.1 (hr 1 (by norm_num)) (hr 2 (by norm_num))).1
    rw [this, strongWords_size]; exact hj)

theorem prep_hWord
    {w : List ℤ} (hw : plettersOK 17 w = true) :
    PRep hnsData.n (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) w)
      (permJ (hWordJ w)) := by
  rw [permJ_hWordJ, ← evalWord_ptoLetters_eq hPerm w hw]
  exact prep_pword (fun h hh => hStrong_rep h hh) (fun h hh => hStrongInv_rep h hh) w hw

theorem seedWordArr_cons (n : ℕ) (a0 a1 : Array ℕ) (l : ℕ) (w : List ℕ) :
    seedWordArr n a0 a1 (l :: w) = pcomp n (if l = 1 then a0 else a1) (seedWordArr n a0 a1 w) :=
  rfl

theorem prep_seedWordArr (w : List ℕ) (hw : ∀ l ∈ w, l = 1 ∨ l = 2) :
    PRep hnsData.n (seedWordArr hnsData.n (natTab (hnsData.orbit ()).alpha)
      (natTab (hnsData.orbit ()).beta) w) (permJ (seedWordJ w)) := by
  induction w with
  | nil =>
    rw [show seedWordJ [] = 1 from rfl, map_one]
    exact prep_pid
  | cons l w ih =>
    rw [seedWordArr_cons, seedWordJ_cons, map_mul]
    refine prep_pcomp ?_ (ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    rcases hw l (List.mem_cons_self ..) with rfl | rfl
    · rw [ite_eq_left rfl, ite_eq_left rfl, permJ_aJ]
      exact prep_a0
    · rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num), permJ_bJ]
      exact prep_a1

@[irreducible] def c1Arrs : Array (Array ℕ) :=
  FAData.c1Words.map fun w => pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) w

theorem c1Arrs_eq : c1Arrs =
    FAData.c1Words.map fun w => pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) w := by
  unfold c1Arrs; rfl

@[irreducible] def g3Arr : Array ℕ :=
  pcomp hnsData.n (seedWordArr hnsData.n (natTab (hnsData.orbit ()).alpha)
    (natTab (hnsData.orbit ()).beta) FAData.g3Root)
    (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) FAData.g3H)

theorem g3Arr_eq : g3Arr = pcomp hnsData.n (seedWordArr hnsData.n (natTab (hnsData.orbit ()).alpha)
    (natTab (hnsData.orbit ()).beta) FAData.g3Root)
    (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) FAData.g3H) := by
  unfold g3Arr; rfl

@[irreducible] def c3Arrs : Array (Array ℕ) :=
  (FAData.c3Words.map fun w => pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) w).push g3Arr

theorem c3Arrs_eq : c3Arrs =
    (FAData.c3Words.map fun w => pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) w).push
      g3Arr := by
  unfold c3Arrs; rfl

@[irreducible] def tree0 : Tree := treeBFS hnsData.n 0 (c1Arrs.map toTable)
  (Array.range (c1Arrs.map toTable).size)

theorem tree0_eq : tree0 = treeBFS hnsData.n 0 (c1Arrs.map toTable)
    (Array.range (c1Arrs.map toTable).size) := by unfold tree0; rfl

@[irreducible] def tree1 : Tree := treeBFS hnsData.n 1047 (c1Arrs.map toTable)
  (Array.range (c1Arrs.map toTable).size)

theorem tree1_eq : tree1 = treeBFS hnsData.n 1047 (c1Arrs.map toTable)
    (Array.range (c1Arrs.map toTable).size) := by unfold tree1; rfl

@[irreducible] def tree2 : Tree := treeBFS hnsData.n 119497 (c1Arrs.map toTable)
  (Array.range (c1Arrs.map toTable).size)

theorem tree2_eq : tree2 = treeBFS hnsData.n 119497 (c1Arrs.map toTable)
    (Array.range (c1Arrs.map toTable).size) := by unfold tree2; rfl

@[irreducible] def tree3 : Tree := treeBFS hnsData.n 0 (c3Arrs.map toTable)
  (Array.range (c3Arrs.map toTable).size)

theorem tree3_eq : tree3 = treeBFS hnsData.n 0 (c3Arrs.map toTable)
    (Array.range (c3Arrs.map toTable).size) := by unfold tree3; rfl

theorem three_parts :
    (∀ k < 4, plettersOK 17 FAData.sWords[k]! = true ∧
      fixListOK hnsData.n (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr)
        FAData.sWords[k]!) FAData.sFixed[k]! = true) ∧
    FAData.c1Words.size = 8 ∧ FAData.c3Words.size = 6 ∧
    (∀ j < 8, plettersOK 17 FAData.c1Words[j]! = true ∧
      peq hnsData.n (pcomp hnsData.n c1Arrs[j]! (pword hnsData.n hStrongArr
        (pinvs hnsData.n hStrongArr) FAData.sWords[0]!)) (pcomp hnsData.n (pword hnsData.n
        hStrongArr (pinvs hnsData.n hStrongArr) FAData.sWords[0]!) c1Arrs[j]!) = true) ∧
    (∀ j < 6, plettersOK 17 FAData.c3Words[j]! = true) ∧ plettersOK 17 FAData.g3H = true ∧
    FAData.g3Root.all (fun l => l == 1 || l == 2) = true ∧
    (∀ j < 7, peq hnsData.n (pcomp hnsData.n c3Arrs[j]! (pword hnsData.n hStrongArr
        (pinvs hnsData.n hStrongArr) FAData.sWords[2]!)) (pcomp hnsData.n (pword hnsData.n
        hStrongArr (pinvs hnsData.n hStrongArr) FAData.sWords[2]!) c3Arrs[j]!) = true) ∧
    (c1Arrs.map toTable).size = 8 ∧ (c3Arrs.map toTable).size = 7 ∧
    (c1Arrs.map toTable).all (fun t => t.size == hnsData.n) = true ∧
    (c3Arrs.map toTable).all (fun t => t.size == hnsData.n) = true ∧
    treeOK hnsData.n 0 tree0 (c1Arrs.map toTable) (Array.range (c1Arrs.map toTable).size) = true ∧
    treeOK hnsData.n 1047 tree1 (c1Arrs.map toTable)
      (Array.range (c1Arrs.map toTable).size) = true ∧
    treeOK hnsData.n 119497 tree2 (c1Arrs.map toTable)
      (Array.range (c1Arrs.map toTable).size) = true ∧
    treeOK hnsData.n 0 tree3 (c3Arrs.map toTable) (Array.range (c3Arrs.map toTable).size) = true ∧
    tree0.pts.size = 1 ∧ tree1.pts.size = 560 ∧ tree2.pts.size = 84 ∧ tree3.pts.size = 60 ∧
    (FAData.sFixed[0]!).all (fun x => inTree tree0 x || inTree tree1 x || inTree tree2 x) =
      true := by
  have h := three_cert
  unfold threeChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [← hRegs_eq, ← hStrongArr_eq, ← c1Arrs_eq, ← g3Arr_eq, ← c3Arrs_eq, ← tree0_eq, ← tree1_eq,
    ← tree2_eq, ← tree3_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩ := h
  refine ⟨fun k hk => ?_, h6, h7, fun j hj => ?_, fun j hj => allBelowN_spec h9 hj, h10, h11,
    fun j hj => allBelowN_spec h12 hj, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24,
    h25⟩
  · have := allBelowN_spec h5 hk
    simp only [Bool.and_eq_true] at this
    exact this
  · have := allBelowN_spec h8 hj
    simp only [Bool.and_eq_true] at this
    exact this

end CFSG.Sporadic.HNSchreier
