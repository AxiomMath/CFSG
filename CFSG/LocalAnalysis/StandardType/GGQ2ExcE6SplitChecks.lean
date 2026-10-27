module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitDefs
import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitCensus
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusTabs

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus

private def insData : List (ℕ × List ℕ × ℕ) :=
  [(1, [0], 0), (4, [2], 0), (16, [4], 0), (21, [0, 2], 0), (32, [5], 0), (64, [6], 0),
    (128, [7], 0), (164, [2, 5], 0), (256, [8], 0), (289, [0, 5], 0), (400, [4, 7], 0),
    (512, [9], 0), (577, [0, 6], 0), (1292, [2, 3], 0), (6660, [2, 9], 0), (8192, [13], 0),
    (8260, [2, 6], 0), (8720, [4, 9], 0), (16384, [14], 0), (16704, [6, 8], 0), (16928, [5, 9], 0),
    (36944, [4, 6], 0), (43009, [0, 11], 0), (47701, [0, 2, 6], 0), (65592, [3, 4], 0),
    (66689, [0, 7], 0), (67005, [0, 2, 3], 0), (131170, [1, 5], 0), (233594, [1, 3, 4], 65),
    (262144, [18], 0), (262336, [6, 7], 0), (270368, [5, 13], 0), (278544, [4, 14], 0),
    (524288, [19], 0), (524928, [7, 9], 0), (532736, [8, 13], 0), (540676, [2, 14], 0),
    (786433, [0, 18], 0), (1056898, [1, 7], 0), (1158275, [0, 1, 7], 68), (1441796, [2, 17], 0),
    (1450214, [1, 2, 5], 0), (2117760, [7, 12], 0), (2392320, [8, 15], 0), (2413008, [4, 6, 7], 0),
    (2623520, [5, 11], 0), (2644644, [2, 5, 9], 0), (2926881, [0, 5, 11], 0),
    (3573004, [2, 3, 15], 75), (4218888, [3, 13], 0), (4522496, [9, 16], 0),
    (4547128, [3, 4, 9], 0), (4719680, [6, 10], 0), (4744524, [2, 3, 6], 0),
    (5048001, [0, 6, 7], 0), (5708292, [2, 9, 16], 57), (6949986, [1, 5, 10], 4),
    (7368842, [1, 3, 7], 1), (8389378, [1, 8], 0), (8396558, [1, 2, 3], 64), (8536065, [0, 14], 0),
    (8536931, [0, 1, 5], 0), (9961488, [4, 19], 0), (9970578, [1, 4, 7], 0),
    (10371093, [0, 2, 14], 0), (10704001, [0, 7, 12], 79), (12126264, [3, 4, 11], 76),
    (12773385, [0, 3, 11], 61), (14193744, [4, 6, 10], 35), (15041282, [1, 8, 15], 3),
    (16777215, [0, 1, 2, 3], 0)]

private def allN (n : ℕ) (f : ℕ → Bool) : Bool := (List.range n).all f

private def anyN (n : ℕ) (f : ℕ → Bool) : Bool := (List.range n).any f

private abbrev dg (c k : ℕ) : ℕ := ExcRaw.Chk.dig c k

private def comb4 (cv cy a b : ℕ) : ℕ :=
  (a * dg cv 0 + b * dg cy 0) % 3 + (a * dg cv 1 + b * dg cy 1) % 3 * 3 +
    (a * dg cv 2 + b * dg cy 2) % 3 * 9 + (a * dg cv 3 + b * dg cy 3) % 3 * 27

private def hmN (i k : ℕ) : ℕ := (ExcRaw.Chk.hN 1 i k % 3).toNat

private def corootN (i : ℕ) : ℕ := hmN i 0 + hmN i 1 * 3 + hmN i 2 * 9 + hmN i 3 * 27

private def centMaskN (n : ℕ) : ℕ :=
  (List.range 24).foldl (fun acc t => if n.testBit t then acc &&& e6SplitKerTab.getD t 0 else acc)
    (2 ^ 81 - 1)

private def fixB (i : ℕ) : Bool := ExcRaw.tabFix1.getD i false

private def gammaN (i : ℕ) : Fin Tag.E6.rank → ℤ :=
  fun k => (e6SplitRootTable.getD i []).getD k.val 0

private def nbrOK : Bool := e6SplitCodeMasks.all fun n =>
  (allN 24 fun i => !n.testBit i || fixB i) ||
  allN 24 fun i => !(n.testBit i && fixB i) ||
    anyN 24 fun j => n.testBit j && !fixB j && iformE6 (gammaN j) (gammaN i) != 0

private def spanMaskN (B : List ℕ) : ℕ :=
  (B.foldl (fun S i => S.flatMap fun u => [u, comb4 u (corootN i) 1 1, comb4 u (corootN i) 1 2])
    [0]).foldl (fun acc u => acc ||| 1 <<< u) 0

private def orthN (n k : ℕ) : Bool := allN 24 fun i => !n.testBit i ||
  (iformE6 (gammaN k) (gammaN i) == 0 &&
    iformE6 (gammaN k) (permLattice (τ := .E6) TwistTag.E6.perm (gammaN i)) == 0)

private def orthKerMaskN (n : ℕ) : ℕ :=
  (List.range 24).foldl (fun acc k => if orthN n k then acc &&& e6SplitKerTab.getD k 0 else acc)
    (2 ^ 81 - 1)

private def insOKAt (n : ℕ) (B : List ℕ) (w₀ : ℕ) : Bool :=
  B.all (fun i => n.testBit i) &&
    if w₀ == 0 then orthKerMaskN n &&& spanMaskN B == orthKerMaskN n
    else ExcRaw.Chk.cardN 24 n == 9 && ExcRaw.Chk.longN 24 n == 6 &&
      (centMaskN n).testBit w₀ &&
      allN 81 fun u => anyN 3 fun l => (spanMaskN B).testBit (comb4 u w₀ 1 (3 - l))

private def insOK : Bool := e6SplitCodeMasks.all fun n =>
  (allN 24 fun i => !n.testBit i || fixB i) ||
  insData.any fun e => e.1 == n && insOKAt n e.2.1 e.2.2

private theorem nbrOK_eq : nbrOK = true := by decide +kernel

private theorem insOK_eq : insOK = true := by decide +kernel

private theorem comb4_eq_combN (cv cy a b : ℕ) :
    comb4 cv cy a b = ExcRaw.Chk.combN 4 cv cy a b := by
  unfold comb4 ExcRaw.Chk.combN ExcRaw.Chk.ofDigits
  simp only [ExcRaw.Chk.dig]
  norm_num [Nat.fold_succ, Nat.fold_zero]

private theorem vec_comb4 (cv cy a b : ℕ) :
    ExcRaw.vec 1 (comb4 cv cy a b) = (a : ZMod 3) • ExcRaw.vec 1 cv +
      (b : ZMod 3) • ExcRaw.vec 1 cy := by
  rw [comb4_eq_combN]
  exact ExcRaw.vec_combN 1 cv cy a b

private theorem comb4_lt (cv cy a b : ℕ) : comb4 cv cy a b < 81 := by
  rw [comb4_eq_combN]
  exact ExcRaw.combN_lt 1 cv cy a b

private theorem vec_corootN (i : ExcRaw.Root 1) :
    ExcRaw.vec 1 (corootN i.val) = ExcRaw.coroot 1 i := by
  revert i
  decide +kernel

private theorem natCast_three_sub (r : ℕ) (hr : r < 3) :
    ((3 - r : ℕ) : ZMod 3) = -(r : ZMod 3) := by
  interval_cases r <;> decide


private theorem allN_eq_true {n : ℕ} {f : ℕ → Bool} :
    allN n f = true ↔ ∀ i < n, f i = true := by
  rw [allN, List.all_eq_true]
  exact ⟨fun h i hi => h i (List.mem_range.mpr hi),
    fun h i hi => h i (List.mem_range.mp hi)⟩

private theorem anyN_eq_true {n : ℕ} {f : ℕ → Bool} :
    anyN n f = true ↔ ∃ i < n, f i = true := by
  rw [anyN, List.any_eq_true]
  exact ⟨fun ⟨i, hi, h⟩ => ⟨i, List.mem_range.mp hi, h⟩,
    fun ⟨i, hi, h⟩ => ⟨i, List.mem_range.mpr hi, h⟩⟩

private theorem testBit_foldl_lor (l : List ℕ) (start v : ℕ) :
    (l.foldl (fun acc u => acc ||| 1 <<< u) start).testBit v = true ↔
      start.testBit v = true ∨ v ∈ l := by
  induction l generalizing start with
  | nil => simp
  | cons a as ih =>
    rw [List.foldl_cons, ih, Nat.testBit_lor, Nat.one_shiftLeft, Nat.testBit_two_pow,
      Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
    tauto

private theorem testBit_foldl_ker (p : ℕ → Bool) (l : List ℕ) (start u : ℕ) :
    (l.foldl (fun acc t => if p t then acc &&& e6SplitKerTab.getD t 0 else acc)
      start).testBit u = true ↔
      start.testBit u = true ∧
        ∀ t ∈ l, p t = true → (e6SplitKerTab.getD t 0).testBit u = true := by
  induction l generalizing start with
  | nil => simp
  | cons a as ih =>
    rw [List.foldl_cons, ih]
    by_cases hp : p a = true
    · rw [if_pos hp, Nat.testBit_land, Bool.and_eq_true]
      constructor
      · rintro ⟨⟨hs, ha⟩, hall⟩
        refine ⟨hs, fun t ht hpt => ?_⟩
        rcases List.mem_cons.mp ht with rfl | ht'
        · exact ha
        · exact hall t ht' hpt
      · rintro ⟨hs, hall⟩
        exact ⟨⟨hs, hall a (List.mem_cons_self ..) hp⟩,
          fun t ht hpt => hall t (List.mem_cons_of_mem a ht) hpt⟩
    · rw [if_neg hp]
      constructor
      · rintro ⟨hs, hall⟩
        refine ⟨hs, fun t ht hpt => ?_⟩
        rcases List.mem_cons.mp ht with rfl | ht'
        · exact absurd hpt hp
        · exact hall t ht' hpt
      · rintro ⟨hs, hall⟩
        exact ⟨hs, fun t ht hpt => hall t (List.mem_cons_of_mem a ht) hpt⟩

private theorem centMaskN_testBit (n u : ℕ) :
    (centMaskN n).testBit u = true ↔
      u < 81 ∧ ∀ t, t < 24 → n.testBit t = true →
        (e6SplitKerTab.getD t 0).testBit u = true := by
  have h := testBit_foldl_ker (fun t => n.testBit t) (List.range 24) (2 ^ 81 - 1) u
  rw [centMaskN]
  exact h.trans (by simp only [Nat.testBit_two_pow_sub_one, decide_eq_true_eq, List.mem_range])

private theorem orthKerMaskN_testBit (n u : ℕ) :
    (orthKerMaskN n).testBit u = true ↔
      u < 81 ∧ ∀ t, t < 24 → orthN n t = true →
        (e6SplitKerTab.getD t 0).testBit u = true := by
  have h := testBit_foldl_ker (fun t => orthN n t) (List.range 24) (2 ^ 81 - 1) u
  rw [orthKerMaskN]
  exact h.trans (by simp only [Nat.testBit_two_pow_sub_one, decide_eq_true_eq, List.mem_range])

private theorem spanMaskN_testBit (B : List ℕ) (u : ℕ) :
    (spanMaskN B).testBit u = true ↔
      u ∈ B.foldl (fun S i => S.flatMap fun u =>
        [u, comb4 u (corootN i) 1 1, comb4 u (corootN i) 1 2]) [0] := by
  rw [spanMaskN, testBit_foldl_lor]
  simp

private theorem spanList_invariant {n : ℕ} {c : Finset (ExcRaw.Root 1)}
    (hcn : c = ExcRaw.ofMask 1 n) :
    ∀ B : List ℕ, (∀ i ∈ B, n.testBit i = true) → (∀ i ∈ B, i < 24) →
      ∀ S : List ℕ, (∀ u ∈ S, u < 81 ∧ ExcRaw.vec 1 u ∈ ExcRaw.inside 1 c) →
        ∀ u ∈ B.foldl (fun S i => S.flatMap fun u =>
          [u, comb4 u (corootN i) 1 1, comb4 u (corootN i) 1 2]) S,
          u < 81 ∧ ExcRaw.vec 1 u ∈ ExcRaw.inside 1 c := by
  intro B
  induction B with
  | nil => intro _ _ S hS u hu; exact hS u hu
  | cons i B ih =>
    intro hB hBlt S hS u hu
    rw [List.foldl_cons] at hu
    have hi24 : i < 24 := hBlt i (List.mem_cons_self ..)
    have hi24' : i < ExcRaw.nroots 1 := by rw [show ExcRaw.nroots 1 = 24 from rfl]; exact hi24
    have hni : n.testBit i = true := hB i (List.mem_cons_self ..)
    have hci : (⟨i, hi24'⟩ : ExcRaw.Root 1) ∈ c := by
      rw [hcn, ExcRaw.mem_ofMask]
      exact hni
    have hcoroot : ExcRaw.coroot 1 ⟨i, hi24'⟩ ∈ ExcRaw.inside 1 c := by
      rw [ExcRaw.inside]
      exact Submodule.subset_span ⟨⟨i, hi24'⟩, hci, rfl⟩
    have hcor : ExcRaw.vec 1 (corootN i) = ExcRaw.coroot 1 ⟨i, hi24'⟩ :=
      vec_corootN ⟨i, hi24'⟩
    refine ih (fun j hj => hB j (List.mem_cons_of_mem i hj))
      (fun j hj => hBlt j (List.mem_cons_of_mem i hj)) (S.flatMap fun u =>
        [u, comb4 u (corootN i) 1 1, comb4 u (corootN i) 1 2]) ?_ u hu
    intro v hv
    obtain ⟨u', hu'S, hv'⟩ := List.mem_flatMap.mp hv
    have hbase := hS u' hu'S
    simp only [List.mem_cons] at hv'
    rcases hv' with rfl | rfl | rfl | hv'
    · exact hbase
    · refine ⟨comb4_lt u' (corootN i) 1 1, ?_⟩
      have hvec : ExcRaw.vec 1 (comb4 u' (corootN i) 1 1) =
          ExcRaw.vec 1 u' + (1 : ZMod 3) • ExcRaw.coroot 1 ⟨i, hi24'⟩ := by
        rw [vec_comb4, hcor]
        simp
      rw [hvec]
      exact Submodule.add_mem _ hbase.2 (Submodule.smul_mem _ _ hcoroot)
    · refine ⟨comb4_lt u' (corootN i) 1 2, ?_⟩
      have hvec : ExcRaw.vec 1 (comb4 u' (corootN i) 1 2) =
          ExcRaw.vec 1 u' + (2 : ZMod 3) • ExcRaw.coroot 1 ⟨i, hi24'⟩ := by
        rw [vec_comb4, hcor]
        simp
      rw [hvec]
      exact Submodule.add_mem _ hbase.2 (Submodule.smul_mem _ _ hcoroot)
    · exact absurd hv' (by simp)

private theorem insData_bound : ∀ e ∈ insData, ∀ i ∈ e.2.1, i < 24 := by
  have h : (insData.all fun e => e.2.1.all fun i => decide (i < 24)) = true := by
    decide +kernel
  intro e he i hi
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h e he) i hi)

private theorem insOKAt_spec {n w : ℕ} {B : List ℕ} (h : insOKAt n B w = true) :
    (∀ i ∈ B, n.testBit i = true) ∧
    (w = 0 → orthKerMaskN n &&& spanMaskN B = orthKerMaskN n) ∧
    (w ≠ 0 → ExcRaw.Chk.cardN 24 n = 9 ∧ ExcRaw.Chk.longN 24 n = 6 ∧
      (centMaskN n).testBit w = true ∧
      ∀ u < 81, ∃ l < 3, (spanMaskN B).testBit (comb4 u w 1 (3 - l)) = true) := by
  unfold insOKAt at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hB, hrest⟩ := h
  have hBall : ∀ i ∈ B, n.testBit i = true := List.all_eq_true.mp hB
  by_cases hw : w = 0
  · have hrest' : (orthKerMaskN n &&& spanMaskN B == orthKerMaskN n) = true := by
      rwa [if_pos (beq_iff_eq.mpr hw)] at hrest
    refine ⟨hBall, fun _ => beq_iff_eq.mp hrest', fun hw' => absurd hw hw'⟩
  · have hrest' : ((ExcRaw.Chk.cardN 24 n == 9) && (ExcRaw.Chk.longN 24 n == 6) &&
        (centMaskN n).testBit w &&
        allN 81 (fun u => anyN 3 fun l =>
          (spanMaskN B).testBit (comb4 u w 1 (3 - l)))) = true := by
      rwa [if_neg (by simpa using hw)] at hrest
    simp only [Bool.and_eq_true] at hrest'
    obtain ⟨⟨⟨hc9, hl6⟩, hcw⟩, hall⟩ := hrest'
    refine ⟨hBall, fun hw' => absurd hw' hw, fun _ => ⟨beq_iff_eq.mp hc9, beq_iff_eq.mp hl6,
      hcw, fun u hu => ?_⟩⟩
    exact anyN_eq_true.mp ((allN_eq_true.mp hall) u hu)

private def longMask : ℕ := 15965194

private theorem longMask_testBit (t : ℕ) (ht : t < 24) :
    longMask.testBit t = ExcRaw.tabFix1.getD t false := by
  have h : ((List.range 24).all fun s =>
      (longMask.testBit s == ExcRaw.tabFix1.getD s false)) = true := by
    decide +kernel
  exact beq_iff_eq.mp (List.all_eq_true.mp h t (List.mem_range.mpr ht))

private theorem filter_long_eq {n : ℕ} {c : Finset (ExcRaw.Root 1)}
    (hcn : c = ExcRaw.ofMask 1 n) :
    c.filter (fun i => ExcRaw.tabFix1.getD i.val false = true) =
      ExcRaw.ofMask 1 (n &&& longMask) := by
  ext t
  simp only [Finset.mem_filter, hcn, ExcRaw.mem_ofMask,
    Nat.testBit_land, longMask_testBit t t.isLt, Bool.and_eq_true]

private theorem longCount_eq_longN {n : ℕ} {c : Finset (ExcRaw.Root 1)}
    (hcn : c = ExcRaw.ofMask 1 n) :
    ExcRaw.longCount 1 c = ExcRaw.Chk.longN 24 n := by
  rw [ExcRaw.longCount, filter_long_eq hcn, ExcRaw.card_ofMask]
  show (List.range 24).countP (fun t => (n &&& longMask).testBit t) =
    (List.range 24).countP (fun t => n.testBit t && ExcRaw.tabFix1.getD t false)
  refine List.countP_congr fun t ht => ?_
  rw [List.mem_range] at ht
  rw [Nat.testBit_land, longMask_testBit t ht]

private theorem not_all_long_of_admissible {c : Finset (ExcRaw.Root 1)}
    (hc : ExcRaw.admissible 1 c) :
    ¬ ∀ i ∈ c, ExcRaw.tabFix1.getD i.val false = true := by
  intro hall
  have hlong : ExcRaw.longCount 1 c = c.card := by
    rw [ExcRaw.longCount, Finset.filter_true_of_mem hall]
  have hlabel : ExcRaw.label 1 c = ExcRaw.labelE6Rel c.card c.card := by
    rw [show ExcRaw.label 1 c =
      ExcRaw.labelE6Rel c.card (ExcRaw.longCount 1 c) from rfl, hlong]
  have hΛ := hc.2
  rw [hlabel] at hΛ
  obtain ⟨U, hU⟩ := hc.1
  have htype := e6Split_type_mem_of_occurs hU
  rw [hlong] at htype
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at htype
  have h13 : c.card = 1 ∨ c.card = 3 := by
    rcases htype with h | h | h | h | h | h | h | h <;> omega
  rcases h13 with h1 | h3
  · rw [h1] at hΛ
    exact absurd hΛ (by simp [LargeEvenInLambda2, ExcRaw.labelE6Rel])
  · rw [h3] at hΛ
    exact absurd hΛ (by simp [LargeEvenInLambda2, ExcRaw.labelE6Rel])

private theorem first_disjunct_false {n : ℕ} {c : Finset (ExcRaw.Root 1)}
    (hcn : c = ExcRaw.ofMask 1 n)
    (h : ¬ ∀ i ∈ c, ExcRaw.tabFix1.getD i.val false = true) :
    allN 24 (fun i => !n.testBit i || fixB i) = false := by
  cases hA : allN 24 (fun i => !n.testBit i || fixB i) with
  | false => rfl
  | true =>
    exfalso
    apply h
    intro i hi
    have hni : n.testBit i.val = true := by
      have := hcn ▸ hi
      simpa using (ExcRaw.mem_ofMask.mp this)
    have hf := (allN_eq_true.mp hA) i.val i.isLt
    rw [hni] at hf
    simpa [fixB] using hf

theorem e6Split_exists_short_adj_of_admissible {c : Finset (ExcRaw.Root 1)}
    (hc : ExcRaw.admissible 1 c) {i : ExcRaw.Root 1} (hi : i ∈ c)
    (hlong : ExcRaw.tabFix1.getD i.val false = true) :
    ∃ j ∈ c, ExcRaw.tabFix1.getD j.val false = false ∧
      iform (e6SplitRoot j) (e6SplitRoot i) ≠ 0 := by
  obtain ⟨U, hU⟩ := hc.1
  obtain ⟨n, hn, hcn⟩ := exists_mem_e6SplitCodeMasks_of_occurs hU
  have hfirst := first_disjunct_false hcn (not_all_long_of_admissible hc)
  have hOK : nbrOK = true := nbrOK_eq
  unfold nbrOK at hOK
  have hmem := (List.all_eq_true.mp hOK) n hn
  rw [hfirst] at hmem
  have hB : (allN 24 fun i => !(n.testBit i && fixB i) ||
      anyN 24 fun j => n.testBit j && !fixB j &&
        iformE6 (gammaN j) (gammaN i) != 0) = true := by
    simpa using hmem
  have hi24 : i.val < 24 := i.isLt
  have hni : n.testBit i.val = true := by
    have := hcn ▸ hi
    simpa using (ExcRaw.mem_ofMask.mp this)
  have hfixi : fixB i.val = true := hlong
  have hC : (anyN 24 fun j => n.testBit j && !fixB j &&
      iformE6 (gammaN j) (gammaN i.val) != 0) = true := by
    have h := (allN_eq_true.mp hB) i.val hi24
    rw [hni, hfixi] at h
    simpa using h
  obtain ⟨j, hj24, hj⟩ := anyN_eq_true.mp hC
  have hj24' : j < ExcRaw.nroots 1 := by
    rw [show ExcRaw.nroots 1 = 24 from rfl]
    exact hj24
  simp only [Bool.and_eq_true, bne_iff_ne] at hj
  obtain ⟨⟨hj1, hj2⟩, hj3⟩ := hj
  have hfixj : fixB j = false := by simpa using hj2
  have hjc : (⟨j, hj24'⟩ : ExcRaw.Root 1) ∈ c := by
    rw [hcn, ExcRaw.mem_ofMask]
    simpa using hj1
  refine ⟨⟨j, hj24'⟩, hjc, by simpa [fixB] using hfixj, ?_⟩
  intro h
  rw [iform_eq_iformE6] at h
  exact hj3 h

theorem e6Split_inside_check {c : Finset (ExcRaw.Root 1)} (hc : ExcRaw.admissible 1 c) :
    ((c.card, ExcRaw.longCount 1 c) = (9, 6) ∧ ExcRaw.inside 1 c ⊔ ExcRaw.cent 1 c = ⊤) ∨
      ∀ v : ExcRaw.V 1, (∀ k : ExcRaw.Root 1,
        (∀ δ ∈ e6SplitCodeRoots c, iform (e6SplitRoot k) δ = 0) → ExcRaw.root 1 k v = 0) →
        v ∈ ExcRaw.inside 1 c := by
  obtain ⟨U, hU⟩ := hc.1
  obtain ⟨n, hn, hcn⟩ := exists_mem_e6SplitCodeMasks_of_occurs hU
  have hfirst := first_disjunct_false hcn (not_all_long_of_admissible hc)
  have hOK : insOK = true := insOK_eq
  unfold insOK at hOK
  have hmem := (List.all_eq_true.mp hOK) n hn
  rw [hfirst] at hmem
  have hdata : (insData.any fun e => e.1 == n && insOKAt n e.2.1 e.2.2) = true := by
    simpa using hmem
  obtain ⟨e, he, hins⟩ := List.any_eq_true.mp hdata
  simp only [Bool.and_eq_true] at hins
  obtain ⟨he1, hinsAt⟩ := hins
  obtain ⟨hBall, hspec0, hspec⟩ := insOKAt_spec hinsAt
  have hB : ∀ i ∈ e.2.1, n.testBit i = true := hBall
  have hBlt : ∀ i ∈ e.2.1, i < 24 := fun i hi => insData_bound e he i hi
  have hinit : ∀ x ∈ ([0] : List ℕ), x < 81 ∧ ExcRaw.vec 1 x ∈ ExcRaw.inside 1 c := by
    intro x hx
    rw [List.mem_singleton] at hx
    rw [hx]
    exact ⟨by norm_num, by rw [ExcRaw.vec_zero]; exact Submodule.zero_mem _⟩
  by_cases hw : e.2.2 = 0
  · right
    intro v hv
    set u := ExcRaw.code 1 v with hu_def
    have hu : u < 81 := by
      rw [hu_def]
      have h := ExcRaw.code_lt 1 v
      rw [show ExcRaw.dim 1 = 4 from rfl] at h
      norm_num at h
      exact h
    have hvec : ExcRaw.vec 1 u = v := by
      rw [hu_def]
      exact ExcRaw.vec_code 1 v
    have hneg : ∀ x y : Fin Tag.E6.rank → ℤ, iform x (-y) = -iform x y := by
      intro x y
      simp [CFSG.LieType.Steinberg.Adjoint.iform, Finset.sum_neg_distrib]
    have hgi : ∀ i : ExcRaw.Root 1, gammaN i.val = e6SplitRoot i := fun i => rfl
    have hroot : ∀ k : ExcRaw.Root 1, orthN n k.val = true → ExcRaw.root 1 k v = 0 := by
      intro k hk
      have hgk : gammaN k.val = e6SplitRoot k := rfl
      refine hv k ?_
      intro δ hδ
      unfold orthN at hk
      have horth : ∀ i : ExcRaw.Root 1, n.testBit i.val = true →
          iformE6 (gammaN k.val) (gammaN i.val) = 0 ∧
            iformE6 (gammaN k.val)
              (permLattice (τ := .E6) TwistTag.E6.perm (gammaN i.val)) = 0 := by
        intro i hni
        have h := (allN_eq_true.mp hk) i.val i.isLt
        rw [hni] at h
        simpa only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] using h
      rcases hδ with ⟨i, hi, hδ | hδ | hδ | hδ⟩
      · have hni : n.testBit i.val = true := by
          have := hcn ▸ hi
          simpa using (ExcRaw.mem_ofMask.mp this)
        have hbase : iform (e6SplitRoot k) (e6SplitRoot i) = 0 := by
          rw [iform_eq_iformE6, ← hgk, ← hgi i]
          exact (horth i hni).1
        rw [hδ]
        exact hbase
      · have hni : n.testBit i.val = true := by
          have := hcn ▸ hi
          simpa using (ExcRaw.mem_ofMask.mp this)
        have hbase : iform (e6SplitRoot k) (e6SplitRoot i) = 0 := by
          rw [iform_eq_iformE6, ← hgk, ← hgi i]
          exact (horth i hni).1
        rw [hδ, hneg (e6SplitRoot k) (e6SplitRoot i), hbase, neg_zero]
      · have hni : n.testBit i.val = true := by
          have := hcn ▸ hi
          simpa using (ExcRaw.mem_ofMask.mp this)
        have hperm : iform (e6SplitRoot k)
            (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i)) = 0 := by
          rw [iform_eq_iformE6, ← hgk, ← hgi i]
          exact (horth i hni).2
        rw [show δ = permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i) from hδ]
        exact hperm
      · have hni : n.testBit i.val = true := by
          have := hcn ▸ hi
          simpa using (ExcRaw.mem_ofMask.mp this)
        have hperm : iform (e6SplitRoot k)
            (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i)) = 0 := by
          rw [iform_eq_iformE6, ← hgk, ← hgi i]
          exact (horth i hni).2
        rw [show δ = -permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i) from hδ,
          hneg (e6SplitRoot k)
            (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i)), hperm, neg_zero]
    have hbit : ∀ t, t < 24 → orthN n t = true →
        (e6SplitKerTab.getD t 0).testBit u = true := by
      intro t ht hk
      have ht' : t < ExcRaw.nroots 1 := by
        rw [show ExcRaw.nroots 1 = 24 from rfl]
        exact ht
      rw [testBit_e6SplitKerTab_iff ⟨t, ht'⟩ hu, hvec]
      exact hroot ⟨t, ht'⟩ hk
    have horthbit : (orthKerMaskN n).testBit u = true := by
      refine (orthKerMaskN_testBit n u).mpr ⟨hu, ?_⟩
      exact fun t ht hk => hbit t ht hk
    have hspan : (spanMaskN e.2.1).testBit u = true := by
      have h1 := congrArg (fun m => m.testBit u) (hspec0 hw)
      rw [Nat.testBit_land] at h1
      simpa [horthbit] using h1
    have hinside := (spanList_invariant hcn e.2.1 hB hBlt [0] hinit u
      ((spanMaskN_testBit e.2.1 u).mp hspan)).2
    rwa [hvec] at hinside
  · left
    obtain ⟨hc9, hl6, hcw, hall⟩ := hspec hw
    have hcard : c.card = 9 := by
      rw [hcn, ExcRaw.card_ofMask]
      show ExcRaw.Chk.cardN 24 n = 9
      exact hc9
    have hlong : ExcRaw.longCount 1 c = 6 := by
      rw [longCount_eq_longN hcn]
      exact hl6
    refine ⟨by rw [hcard, hlong], ?_⟩
    have hwlt : e.2.2 < 81 := ((centMaskN_testBit n e.2.2).mp hcw).1
    have hkerC : ∀ t, t < 24 → n.testBit t = true →
        (e6SplitKerTab.getD t 0).testBit e.2.2 = true :=
      ((centMaskN_testBit n e.2.2).mp hcw).2
    have hcent : ExcRaw.vec 1 e.2.2 ∈ ExcRaw.cent 1 c := by
      rw [ExcRaw.cent]
      simp only [Submodule.mem_iInf, LinearMap.mem_ker]
      intro i hi
      have hni : n.testBit i.val = true := by
        have := hcn ▸ hi
        simpa using (ExcRaw.mem_ofMask.mp this)
      exact (testBit_e6SplitKerTab_iff i hwlt).mp (hkerC i.val i.isLt hni)
    rw [eq_top_iff]
    intro v _
    set u := ExcRaw.code 1 v with hu_def
    have hu : u < 81 := by
      rw [hu_def]
      have h := ExcRaw.code_lt 1 v
      rw [show ExcRaw.dim 1 = 4 from rfl] at h
      norm_num at h
      exact h
    have hvec : ExcRaw.vec 1 u = v := by
      rw [hu_def]
      exact ExcRaw.vec_code 1 v
    obtain ⟨l, hl3, hlbit⟩ := hall u hu
    have hinside : ExcRaw.vec 1 (comb4 u e.2.2 1 (3 - l)) ∈ ExcRaw.inside 1 c :=
      (spanList_invariant hcn e.2.1 hB hBlt [0] hinit _
        ((spanMaskN_testBit e.2.1 _).mp hlbit)).2
    have hdecomp : v = ExcRaw.vec 1 (comb4 u e.2.2 1 (3 - l)) +
        (l : ZMod 3) • ExcRaw.vec 1 e.2.2 := by
      rw [vec_comb4, natCast_three_sub l hl3, hvec, neg_smul]
      simp only [Nat.cast_one, one_smul]
      abel
    rw [hdecomp]
    exact Submodule.add_mem_sup hinside (Submodule.smul_mem _ _ hcent)

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
