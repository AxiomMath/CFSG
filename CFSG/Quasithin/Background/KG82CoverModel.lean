module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolic

public section

namespace CFSG.Quasithin.H.L34Cov

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.ComponentClassification.GrSLit.L34Facts MulAction
open scoped commutatorElement Pointwise

theorem foldl_genS (v : List ℕ) (g : Equiv.Perm (Fin 42)) :
    v.foldl (fun g j => g * genS j) g = g * wordPerm v := by
  induction v generalizing g with
  | nil => simp [wordPerm]
  | cons j v ih =>
    have e : wordPerm (j :: v) = 1 * genS j * wordPerm v := by
      show List.foldl _ 1 (j :: v) = _
      rw [List.foldl_cons, ih]
    rw [List.foldl_cons, ih, e, one_mul, mul_assoc]

theorem wordPerm_append (u v : List ℕ) : wordPerm (u ++ v) = wordPerm u * wordPerm v := by
  rw [wordPerm, List.foldl_append, foldl_genS]
  rfl

theorem wordPerm_singleton (j : ℕ) : wordPerm [j] = genS j := by
  simp [wordPerm]

theorem wordPerm_cons (j : ℕ) (v : List ℕ) : wordPerm (j :: v) = genS j * wordPerm v := by
  rw [show j :: v = [j] ++ v from rfl, wordPerm_append, wordPerm_singleton]

theorem wordPerm_eq_of_tab {u v : List ℕ} (h : wordTab u = wordTab v) :
    wordPerm u = wordPerm v :=
  ((tabRep_wordTab u).eq_iff (tabRep_wordTab v)).1 h

theorem wordPerm_eq_one {w : List ℕ} (h : wordTab w = idTab 42) : wordPerm w = 1 :=
  (tabRep_wordTab w).perm_eq (h ▸ TabRep.idTab)

theorem wordPerm_apply (w : List ℕ) (i : Fin 42) :
    ((wordPerm w i : Fin 42) : ℕ) = (wordTab w)[i.val]! :=
  ((tabRep_wordTab w).apply i).symm

@[expose] def invL (j : ℕ) : List ℕ := if j = 0 then [0, 0] else [j]

@[expose] def invW (w : List ℕ) : List ℕ := (w.reverse.map invL).flatten

theorem invW_cons (j : ℕ) (w : List ℕ) : invW (j :: w) = invW w ++ invL j := by
  simp [invW]

theorem genS_zero : genS 0 = g₁ := rfl

theorem genS_one : genS 1 = g₂ := rfl

theorem genS_two : genS 2 = g₃ := rfl

theorem genS_of_two_le {j : ℕ} (hj : 2 ≤ j) : genS j = g₃ := by
  simp [genS, show j ≠ 0 by omega, show j ≠ 1 by omega]

theorem genS_inv (j : ℕ) : (genS j)⁻¹ = wordPerm (invL j) := by
  have h0 : wordPerm [0, 0, 0] = 1 := wordPerm_eq_one (by decide +kernel)
  have h1 : wordPerm [1, 1] = 1 := wordPerm_eq_one (by decide +kernel)
  have h2 : wordPerm [2, 2] = 1 := wordPerm_eq_one (by decide +kernel)
  rcases Nat.lt_or_ge j 2 with hj | hj
  · interval_cases j
    · rw [show invL 0 = [0, 0] from rfl]
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← h0, show [0, 0, 0] = [0] ++ [0, 0] from rfl, wordPerm_append, wordPerm_singleton]
    · rw [show invL 1 = [1] from rfl, wordPerm_singleton]
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← h1, show [1, 1] = [1] ++ [1] from rfl, wordPerm_append, wordPerm_singleton]
  · have e : genS j = genS 2 := by rw [genS_of_two_le hj, genS_two]
    rw [show invL j = [j] by simp [invL, show j ≠ 0 by omega], wordPerm_singleton, e]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← h2, show [2, 2] = [2] ++ [2] from rfl, wordPerm_append, wordPerm_singleton]

theorem wordPerm_invW (w : List ℕ) : wordPerm (invW w) = (wordPerm w)⁻¹ := by
  induction w with
  | nil => simp [invW, wordPerm]
  | cons j w ih => rw [invW_cons, wordPerm_append, ih, wordPerm_cons, mul_inv_rev, genS_inv]

@[expose] def prodW (ws : List (List ℕ)) (is : List ℕ) : List ℕ := (is.map (ws.getD · [])).flatten

theorem wordPerm_prodW_mem (ws : List (List ℕ)) {is : List ℕ} (his : ∀ i ∈ is, i < ws.length) :
    wordPerm (prodW ws is) ∈ Subgroup.closure (wordSet ws) := by
  induction is with
  | nil => exact Subgroup.one_mem _
  | cons i is ih =>
    rw [prodW, List.map_cons, List.flatten_cons, wordPerm_append]
    refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, ?_, rfl⟩)
      (ih fun k hk => his k (List.mem_cons_of_mem _ hk))
    rw [List.getD_eq_getElem _ _ (his i List.mem_cons_self)]
    exact List.getElem_mem _

theorem wordPerm_mem_closure {ws : List (List ℕ)} {w : List ℕ} (hw : w ∈ ws) :
    wordPerm w ∈ Subgroup.closure (wordSet ws) :=
  Subgroup.subset_closure ⟨w, hw, rfl⟩

@[expose] def LRep (l : List ℕ) (g : Equiv.Perm (Fin 42)) : Prop :=
  l.length = 42 ∧ ∀ i : Fin 42, l.getD i 0 = (g i : ℕ)

@[expose] def lcomp (p q : List ℕ) : List ℕ := q.map fun i => p.getD i 0

theorem LRep.comp {p q : List ℕ} {g h : Equiv.Perm (Fin 42)} (hp : LRep p g) (hq : LRep q h) :
    LRep (lcomp p q) (g * h) := by
  refine ⟨by simp [lcomp, hq.1], fun i => ?_⟩
  have hi : (i : ℕ) < q.length := by rw [hq.1]; exact i.2
  rw [lcomp, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    ← List.getD_eq_getElem _ 0 hi, hq.2 i, hp.2 (h i)]
  rfl

theorem LRep.perm_eq {l : List ℕ} {g h : Equiv.Perm (Fin 42)} (hg : LRep l g) (hh : LRep l h) :
    g = h :=
  Equiv.ext fun i => Fin.ext ((hg.2 i).symm.trans (hh.2 i))

theorem lrep_range : LRep (List.range 42) 1 :=
  ⟨List.length_range, fun i => by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_range]
    rfl⟩

theorem lrep_toList {t : Tab} {g : Equiv.Perm (Fin 42)} (ht : TabRep t g) : LRep t.toList g := by
  refine ⟨by rw [Array.length_toList, ht.1], fun i => ?_⟩
  have hi : (i : ℕ) < t.size := by rw [ht.1]; exact i.2
  rw [List.getD_eq_getElem _ _ (by simpa using hi), Array.getElem_toList, ← ht.apply i]
  exact (getElem!_pos t (i : ℕ) hi).symm

@[expose] def gL : List (List ℕ) :=
  [[5, 0, 6, 8, 7, 1, 9, 17, 13, 2, 10, 20, 15, 3, 11, 18, 16, 4, 12, 19, 14, 26, 21, 27, 29, 28,
      22, 30, 38, 34, 23, 31, 41, 36, 24, 32, 39, 37, 25, 33, 40, 35],
    [0, 9, 10, 11, 12, 5, 6, 7, 8, 1, 2, 3, 4, 17, 19, 20, 18, 13, 16, 14, 15, 21, 22, 23, 24, 25,
      30, 31, 32, 33, 26, 27, 28, 29, 38, 39, 40, 41, 34, 35, 36, 37],
    [0, 17, 20, 18, 19, 5, 6, 7, 8, 13, 15, 16, 14, 9, 12, 10, 11, 1, 3, 4, 2, 21, 22, 23, 24, 25,
      34, 35, 36, 37, 38, 39, 40, 41, 26, 27, 28, 29, 30, 31, 32, 33]]

@[expose] def genL (j : ℕ) : List ℕ := gL.getD (min j 2) []

theorem gL_eq : gL = [g₁T.toList, g₂T.toList, g₃T.toList] := by decide +kernel

theorem lrep_genL (j : ℕ) : LRep (genL j) (genS j) := by
  have h := gL_eq
  rcases Nat.lt_or_ge j 2 with hj | hj
  · interval_cases j
    · rw [show genL 0 = g₁T.toList by rw [genL, h]; rfl]
      exact lrep_toList tabRep_g₁
    · rw [show genL 1 = g₂T.toList by rw [genL, h]; rfl]
      exact lrep_toList tabRep_g₂
  · rw [show genL j = g₃T.toList by rw [genL, h, Nat.min_eq_right hj]; rfl, genS_of_two_le hj]
    exact lrep_toList tabRep_g₃

@[expose] def wordL (w : List ℕ) : List ℕ := w.foldl (fun l j => lcomp l (genL j)) (List.range 42)

theorem lrep_foldl (w : List ℕ) {l : List ℕ} {g : Equiv.Perm (Fin 42)} (hl : LRep l g) :
    LRep (w.foldl (fun l j => lcomp l (genL j)) l) (w.foldl (fun g j => g * genS j) g) := by
  induction w generalizing l g with
  | nil => exact hl
  | cons j w ih =>
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (hl.comp (lrep_genL j))

theorem lrep_wordL (w : List ℕ) : LRep (wordL w) (wordPerm w) := lrep_foldl w lrep_range

theorem eq_of_wordL {u v : List ℕ} (h : wordL u = wordL v) : wordPerm u = wordPerm v :=
  (lrep_wordL u).perm_eq (h ▸ lrep_wordL v)

theorem eq_one_of_wordL {w : List ℕ} (h : wordL w = List.range 42) : wordPerm w = 1 :=
  (lrep_wordL w).perm_eq (h ▸ lrep_range)

theorem apply_of_wordL (w : List ℕ) (i : Fin 42) :
    ((wordPerm w i : Fin 42) : ℕ) = (wordL w).getD i 0 :=
  ((lrep_wordL w).2 i).symm

theorem mem_list_of_closed {gs A : List (List ℕ)} (h1 : [] ∈ A)
    (hcl : ∀ g ∈ gs, ∀ a ∈ A, ∃ a' ∈ A, wordL (g ++ a) = wordL a')
    (hinv : ∀ g ∈ gs, ∀ a ∈ A, ∃ a' ∈ A, wordL (invW g ++ a) = wordL a')
    {x : Equiv.Perm (Fin 42)} (hx : x ∈ Subgroup.closure (wordSet gs)) :
    ∃ a ∈ A, x = wordPerm a := by
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨[], h1, rfl⟩
  | mul_left x hx y _ ih =>
    obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨a, ha, rfl⟩ := ih
    obtain ⟨a', ha', he⟩ := hcl g hg a ha
    exact ⟨a', ha', by rw [← wordPerm_append, eq_of_wordL he]⟩
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨a, ha, rfl⟩ := ih
    obtain ⟨a', ha', he⟩ := hinv g hg a ha
    exact ⟨a', ha', by rw [← wordPerm_invW, ← wordPerm_append, eq_of_wordL he]⟩

@[expose] def treeChk (ts : List Tab) : List ℕ → List (ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | seen, (y, x, j) :: l =>
    seen.contains x && decide (j < ts.length) && (ts.getD j #[])[x]! == y &&
      treeChk ts (y :: seen) l

theorem treeChk_spec (ts : List Tab) (P : ℕ → Prop)
    (hP : ∀ j < ts.length, ∀ x, P x → P ((ts.getD j #[])[x]!)) :
    ∀ (seen : List ℕ) (l : List (ℕ × ℕ × ℕ)), (∀ x ∈ seen, P x) → treeChk ts seen l = true →
      ∀ e ∈ l, P e.1
  | _, [], _, _ => fun _ h => by simp at h
  | seen, (y, x, j) :: l, hs, h => by
    simp only [treeChk, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq,
      beq_iff_eq] at h
    obtain ⟨⟨⟨hx, hj⟩, hy⟩, hl⟩ := h
    have hPy : P y := hy ▸ hP j hj x (hs x hx)
    have ih := treeChk_spec ts P hP (y :: seen) l
      (fun z hz => (List.mem_cons.1 hz).elim (fun e => e ▸ hPy) (hs z)) hl
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact hPy
    · exact ih e he

theorem exists_of_treeChk {H : Subgroup (Equiv.Perm (Fin 42))} {gs : List (Equiv.Perm (Fin 42))}
    {ts : List Tab} (hlen : ts.length = gs.length) (hgs : ∀ g ∈ gs, g ∈ H)
    (hts : ∀ j (hj : j < ts.length), TabRep ts[j] (gs[j]'(hlen ▸ hj))) (r : Fin 42)
    {l : List (ℕ × ℕ × ℕ)} (hl : treeChk ts [r.val] l = true) :
    ∀ e ∈ l, ∃ h ∈ H, ((h r : Fin 42) : ℕ) = e.1 := by
  refine treeChk_spec ts (fun y => ∃ h ∈ H, ((h r : Fin 42) : ℕ) = y) ?_ [r.val] l ?_ hl
  · rintro j hj _ ⟨h, hh, rfl⟩
    refine ⟨gs[j]'(hlen ▸ hj) * h, H.mul_mem (hgs _ (List.getElem_mem _)) hh, ?_⟩
    rw [List.getD_eq_getElem _ _ hj, (hts j hj).apply, Equiv.Perm.mul_apply]
  · intro x hx
    rw [List.mem_singleton] at hx
    exact ⟨1, H.one_mem, by rw [hx]; rfl⟩

@[expose] def ap (x : Equiv.Perm (Fin 42)) (i : ℕ) : ℕ := if h : i < 42 then (x ⟨i, h⟩ : ℕ) else i

theorem ap_of_lt (x : Equiv.Perm (Fin 42)) {i : ℕ} (hi : i < 42) : ap x i = (x ⟨i, hi⟩ : ℕ) := by
  simp only [ap, hi, ↓reduceDIte]

theorem ap_of_not_lt (x : Equiv.Perm (Fin 42)) {i : ℕ} (hi : ¬i < 42) : ap x i = i := by
  simp only [ap, hi, ↓reduceDIte]

theorem ap_lt (x : Equiv.Perm (Fin 42)) {i : ℕ} (hi : i < 42) : ap x i < 42 := by
  rw [ap_of_lt x hi]
  exact (x ⟨i, hi⟩).2

theorem ap_fin (x : Equiv.Perm (Fin 42)) (i : Fin 42) : ap x i = (x i : ℕ) := ap_of_lt x i.2

theorem ap_mul (x y : Equiv.Perm (Fin 42)) (i : ℕ) : ap (x * y) i = ap x (ap y i) := by
  by_cases hi : i < 42
  · rw [ap_of_lt _ hi, ap_of_lt y hi, ap_fin]
    rfl
  · rw [ap_of_not_lt _ hi, ap_of_not_lt y hi, ap_of_not_lt x hi]

theorem ap_of_tabRep {t : Tab} {x : Equiv.Perm (Fin 42)} (ht : TabRep t x) {i : ℕ}
    (hi : i < 42) : ap x i = t[i]! := by
  rw [ap_of_lt x hi, ← ht.apply ⟨i, hi⟩]

@[expose] def flagL : List (ℕ × ℕ) :=
  [(0, 22), (0, 26), (0, 30), (0, 34), (0, 38), (1, 21), (1, 26), (1, 27), (1, 28), (1, 29),
    (2, 23), (2, 26), (2, 31), (2, 36), (2, 41), (3, 25), (3, 26), (3, 33), (3, 35), (3, 40),
    (4, 24), (4, 26), (4, 32), (4, 37), (4, 39), (5, 21), (5, 22), (5, 23), (5, 24), (5, 25),
    (6, 22), (6, 27), (6, 31), (6, 35), (6, 39), (7, 22), (7, 29), (7, 33), (7, 37), (7, 41),
    (8, 22), (8, 28), (8, 32), (8, 36), (8, 40), (9, 21), (9, 30), (9, 31), (9, 32), (9, 33),
    (10, 23), (10, 27), (10, 30), (10, 37), (10, 40), (11, 25), (11, 29), (11, 30), (11, 36),
    (11, 39), (12, 24), (12, 28), (12, 30), (12, 35), (12, 41), (13, 21), (13, 38), (13, 39),
    (13, 40), (13, 41), (14, 24), (14, 27), (14, 33), (14, 36), (14, 38), (15, 23), (15, 29),
    (15, 32), (15, 35), (15, 38), (16, 25), (16, 28), (16, 31), (16, 37), (16, 38), (17, 21),
    (17, 34), (17, 35), (17, 36), (17, 37), (18, 25), (18, 27), (18, 32), (18, 34), (18, 41),
    (19, 24), (19, 29), (19, 31), (19, 34), (19, 40), (20, 23), (20, 28), (20, 33), (20, 34),
    (20, 39)]

@[expose] def Inv42 (x : Equiv.Perm (Fin 42)) : Prop :=
  (∀ i < 21, ap x i < 21) ∧ (∀ i, 21 ≤ i → i < 42 → 21 ≤ ap x i) ∧
    ∀ p ∈ flagL, (ap x p.1, ap x p.2) ∈ flagL

theorem inv42_mul {x y : Equiv.Perm (Fin 42)} (hx : Inv42 x) (hy : Inv42 y) : Inv42 (x * y) := by
  refine ⟨fun i hi => ?_, fun i hi hi' => ?_, fun p hp => ?_⟩
  · rw [ap_mul]
    exact hx.1 _ (hy.1 i hi)
  · rw [ap_mul]
    exact hx.2.1 _ (hy.2.1 i hi hi') (ap_lt y hi')
  · rw [ap_mul, ap_mul]
    exact hx.2.2 _ (hy.2.2 p hp)

@[expose] def inv42Chk (t : Tab) : Bool :=
  (List.range 21).all (fun i => decide (t[i]! < 21)) &&
    (List.range 21).all (fun i => decide (21 ≤ t[i + 21]!)) &&
      flagL.all fun p => flagL.contains (t[p.1]!, t[p.2]!)

theorem inv42_of_chk {t : Tab} {x : Equiv.Perm (Fin 42)} (ht : TabRep t x)
    (h : inv42Chk t = true) : Inv42 x := by
  simp only [inv42Chk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    List.contains_iff_mem] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun i hi => ?_, fun i hi hi' => ?_, fun p hp => ?_⟩
  · rw [ap_of_tabRep ht (by omega)]
    exact h1 i hi
  · rw [ap_of_tabRep ht hi']
    have := h2 (i - 21) (by omega)
    rwa [show i - 21 + 21 = i by omega] at this
  · have hp1 : p.1 < 42 := by
      have : ∀ q ∈ flagL, q.1 < 42 := by decide
      exact this p hp
    have hp2 : p.2 < 42 := by
      have : ∀ q ∈ flagL, q.2 < 42 := by decide
      exact this p hp
    rw [ap_of_tabRep ht hp1, ap_of_tabRep ht hp2]
    exact h3 p hp

theorem inv42_gens : inv42Chk g₁T = true ∧ inv42Chk g₂T = true ∧ inv42Chk g₃T = true := by
  decide +kernel

theorem inv42_of_mem {x : Equiv.Perm (Fin 42)} (hx : x ∈ S) : Inv42 x := by
  have hg : ∀ j, Inv42 (genS j) := by
    intro j
    rcases Nat.lt_or_ge j 2 with hj | hj
    · interval_cases j
      · exact inv42_of_chk tabRep_g₁ inv42_gens.1
      · exact inv42_of_chk tabRep_g₂ inv42_gens.2.1
    · rw [genS_of_two_le hj]
      exact inv42_of_chk tabRep_g₃ inv42_gens.2.2
  have hw : ∀ w, Inv42 (wordPerm w) := by
    intro w
    induction w with
    | nil =>
      have e : ∀ i, ap (wordPerm []) i = i := fun i => by
        by_cases hi : i < 42
        · rw [ap_of_lt _ hi]
          rfl
        · exact ap_of_not_lt _ hi
      refine ⟨fun i hi => ?_, fun i hi _ => ?_, fun p hp => ?_⟩
      · rw [e]
        exact hi
      · rw [e]
        exact hi
      · rw [e, e]
        exact hp
    | cons j w ih => rw [wordPerm_cons]; exact inv42_mul (hg j) ih
  have hgen : ∀ y ∈ ({g₁, g₂, g₃} : Set (Equiv.Perm (Fin 42))), Inv42 y := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact hg 0
    · exact hg 1
    · exact hg 2
  induction hx using Subgroup.closure_induction'' with
  | mem y hy => exact hgen y hy
  | inv_mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · rw [← genS_zero, genS_inv]
      exact hw _
    · rw [← genS_one, genS_inv]
      exact hw _
    · rw [← genS_two, genS_inv]
      exact hw _
  | one => exact hw []
  | mul x y _ _ hx hy => exact inv42_mul hx hy

@[expose] def treeS2 : List (ℕ × ℕ × ℕ) :=
  [(6, 2, 0), (10, 2, 1), (20, 2, 2), (9, 6, 0), (15, 10, 2), (14, 20, 0), (1, 9, 1), (13, 9, 2),
    (18, 15, 0), (11, 14, 0), (19, 14, 1), (12, 14, 2), (0, 1, 0), (17, 1, 2), (3, 13, 0),
    (16, 18, 1), (4, 19, 2), (5, 0, 0), (8, 3, 0), (7, 4, 0)]

@[expose] def treeS23 : List (ℕ × ℕ × ℕ) :=
  [(27, 23, 0), (30, 27, 0), (31, 27, 1), (35, 27, 2), (26, 30, 1), (38, 30, 2), (39, 31, 2),
    (32, 35, 0), (22, 26, 0), (34, 26, 2), (25, 38, 0), (33, 39, 0), (41, 32, 0), (28, 32, 1),
    (40, 32, 2), (21, 22, 0), (24, 34, 0), (36, 33, 0), (29, 33, 1), (37, 41, 1)]

@[expose] def treeT0 : List (List (ℕ × ℕ × ℕ)) :=
  [[(6, 0, 0), (8, 0, 1), (1, 6, 0), (7, 6, 1), (16, 6, 3), (18, 8, 0), (14, 8, 3), (9, 1, 0),
      (17, 1, 1), (13, 7, 3), (4, 16, 0), (3, 16, 2), (11, 18, 2), (12, 18, 3), (19, 9, 3)],
    [(30, 21, 0), (29, 21, 3), (22, 30, 0), (40, 30, 1), (27, 30, 2), (34, 30, 3), (33, 29, 0),
      (35, 29, 1), (32, 29, 2), (38, 22, 3), (25, 40, 0), (37, 40, 2), (28, 27, 3), (39, 34, 2),
      (24, 32, 3)],
    [(10, 5, 0), (15, 5, 3), (20, 10, 3)], [(31, 26, 0), (36, 26, 1), (41, 31, 1)]]

theorem tree_ok : treeChk [g₁T, g₂T, g₃T] [2] treeS2 = true ∧
    treeChk [g₁T, g₂T, g₃T] [23] treeS23 = true ∧
    treeChk (wT₀.map wordTab) [0] (treeT0.getD 0 []) = true ∧
    treeChk (wT₀.map wordTab) [21] (treeT0.getD 1 []) = true ∧
    treeChk (wT₀.map wordTab) [5] (treeT0.getD 2 []) = true ∧
    treeChk (wT₀.map wordTab) [26] (treeT0.getD 3 []) = true := by
  decide +kernel

theorem exists_S_of_tree (r : Fin 42) {l : List (ℕ × ℕ × ℕ)}
    (hl : treeChk [g₁T, g₂T, g₃T] [r.val] l = true) :
    ∀ e ∈ l, ∃ h ∈ S, ((h r : Fin 42) : ℕ) = e.1 :=
  exists_of_treeChk (gs := [g₁, g₂, g₃]) rfl
    (by simp [g₁_mem_S, g₂_mem_S, g₃_mem_S])
    (fun j hj => by
      simp only [List.length_cons, List.length_nil] at hj
      interval_cases j
      exacts [tabRep_g₁, tabRep_g₂, tabRep_g₃]) r hl

theorem exists_T0_of_tree (r : Fin 42) {l : List (ℕ × ℕ × ℕ)}
    (hl : treeChk (wT₀.map wordTab) [r.val] l = true) :
    ∀ e ∈ l, ∃ h ∈ T0, ((h r : Fin 42) : ℕ) = e.1 :=
  exists_of_treeChk (gs := wT₀.map wordPerm) (by simp)
    (fun g hg => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg
      exact Subgroup.subset_closure ⟨w, hw, rfl⟩)
    (fun j hj => by
      simp only [List.getElem_map]
      exact tabRep_wordTab _) r hl

theorem exists_of_cover {H : Subgroup (Equiv.Perm (Fin 42))} {r : Fin 42}
    {l : List (ℕ × ℕ × ℕ)} (hl : ∀ e ∈ l, ∃ h ∈ H, ((h r : Fin 42) : ℕ) = e.1) {y : Fin 42}
    (hy : y = r ∨ ∃ e ∈ l, e.1 = y.val) : ∃ h ∈ H, h r = y := by
  rcases hy with rfl | ⟨e, he, hey⟩
  · exact ⟨1, H.one_mem, rfl⟩
  · obtain ⟨h, hh, hhe⟩ := hl e he
    exact ⟨h, hh, Fin.ext (hhe.trans hey)⟩

theorem smul_eq_apply (x : ↥S) (i : Fin 42) : x • i = (x : Equiv.Perm (Fin 42)) i := rfl

theorem mem_stabilizer_iff' {x : ↥S} {i : Fin 42} :
    x ∈ stabilizer ↥S i ↔ (x : Equiv.Perm (Fin 42)) i = i := Iff.rfl

theorem apply_lt_of_mem {x : Equiv.Perm (Fin 42)} (hx : x ∈ S) {i : Fin 42} (hi : (i : ℕ) < 21) :
    ((x i : Fin 42) : ℕ) < 21 := by
  rw [← ap_fin]
  exact (inv42_of_mem hx).1 i hi

theorem le_apply_of_mem {x : Equiv.Perm (Fin 42)} (hx : x ∈ S) {i : Fin 42}
    (hi : 21 ≤ (i : ℕ)) : 21 ≤ ((x i : Fin 42) : ℕ) := by
  rw [← ap_fin]
  exact (inv42_of_mem hx).2.1 i hi i.2

theorem factorization_960 : (960 : ℕ).factorization 2 = 6 := by
  have h : (960 : ℕ) = 2 ^ 6 * 15 := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 15)]
  simp

theorem factorization_20160' : (20160 : ℕ).factorization 2 = 6 := by
  have h : (20160 : ℕ) = 2 ^ 6 * 315 := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]
  simp

theorem card_stabilizer_of_orbit {r : Fin 42}
    {A : Finset (Fin 42)} (hA : A.card = 21) (horb : orbit ↥S r = ↑A) :
    Nat.card (stabilizer ↥S r) = 960 := by
  have h1 := index_stabilizer ↥S r
  rw [horb, Set.ncard_coe_finset, hA] at h1
  have h2 := (stabilizer ↥S r).card_mul_index
  rw [h1, card_S] at h2
  omega

@[expose] def pts : Finset (Fin 42) := Finset.univ.filter fun y => (y : ℕ) < 21

@[expose] def lns : Finset (Fin 42) := Finset.univ.filter fun y => 21 ≤ (y : ℕ)

theorem orbit_two : orbit ↥S (2 : Fin 42) = ↑pts := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simp only [pts, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    exact apply_lt_of_mem x.2 (i := 2) (by norm_num)
  · intro hy
    have hy' : (y : ℕ) < 21 := by simpa [pts] using hy
    have hcov : ∀ y : Fin 42, (y : ℕ) < 21 → y = 2 ∨ ∃ e ∈ treeS2, e.1 = y.val := by decide
    obtain ⟨h, hh, rfl⟩ := exists_of_cover (exists_S_of_tree 2 tree_ok.1) (hcov y hy')
    exact ⟨⟨h, hh⟩, rfl⟩

theorem orbit_tt : orbit ↥S (23 : Fin 42) = ↑lns := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simp only [lns, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    exact le_apply_of_mem x.2 (i := 23) (by norm_num)
  · intro hy
    have hy' : 21 ≤ (y : ℕ) := by simpa [lns] using hy
    have hcov : ∀ y : Fin 42, 21 ≤ (y : ℕ) → y = 23 ∨ ∃ e ∈ treeS23, e.1 = y.val := by decide
    obtain ⟨h, hh, rfl⟩ := exists_of_cover (exists_S_of_tree 23 tree_ok.2.1) (hcov y hy')
    exact ⟨⟨h, hh⟩, rfl⟩

theorem card_stab_two :
    Nat.card (stabilizer ↥S (2 : Fin 42)) = 960 :=
  card_stabilizer_of_orbit (by decide) orbit_two

theorem card_stab_tt :
    Nat.card (stabilizer ↥S (23 : Fin 42)) = 960 :=
  card_stabilizer_of_orbit (by decide) orbit_tt

theorem closure_eq_stab {ws : List (List ℕ)} {i : Fin 42}
    (hfix : ∀ w ∈ ws, (wordTab w)[i.val]! = i.val)
    (hc : Nat.card (Subgroup.closure (wordSet ws)) = 960)
    (hs : Nat.card (stabilizer ↥S i) = 960) :
    (Subgroup.closure (wordSet ws)).subgroupOf S = stabilizer ↥S i := by
  have hle : (Subgroup.closure (wordSet ws)).subgroupOf S ≤ stabilizer ↥S i := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [mem_stabilizer_iff']
    have h1 : Subgroup.closure (wordSet ws) ≤ stabilizer (Equiv.Perm (Fin 42)) i := by
      rw [Subgroup.closure_le]
      rintro _ ⟨w, hw, rfl⟩
      exact Fin.ext ((wordPerm_apply w i).trans (hfix w hw))
    exact h1 hx
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hs, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (closure_wordSet_le ws)).toEquiv, hc]

theorem P1_eq_stab :
    P1.subgroupOf S = stabilizer ↥S (2 : Fin 42) :=
  closure_eq_stab (by decide +kernel) card_P1 card_stab_two

theorem P2_eq_stab :
    P2.subgroupOf S = stabilizer ↥S (23 : Fin 42) :=
  closure_eq_stab (by decide +kernel) card_P2 card_stab_tt

theorem apply_mem_of_orbit {Q₀ : Subgroup ↥S} (hQ : Nat.card Q₀ = 960) (hT : T0.subgroupOf S ≤ Q₀)
    {r b c : Fin 42} {H B C : Finset (Fin 42)}
    (hH : ∀ y, y ∈ H ↔ y = r ∨ y ∈ B ∨ y ∈ C) (hHc : H.card = 21) (hCc : (insert r C).card = 17)
    (hrB : r ∉ B) (hrC : r ∉ C)
    (hSH : ∀ x ∈ S, x r ∈ H)
    (hB : ∀ y ∈ B, ∃ t ∈ T0, t b = y) (hb : b ∈ B)
    (hC : ∀ y ∈ C, ∃ t ∈ T0, t c = y) (hc : c ∈ C) :
    ∀ x ∈ Q₀, ((x : ↥S) : Equiv.Perm (Fin 42)) r ∈ insert r B := by
  set O := orbit ↥Q₀ r
  have hO : ∀ y ∈ O, y ∈ H := by
    rintro _ ⟨q, rfl⟩
    exact hSH _ (q : ↥S).2
  have hrO : r ∈ O := mem_orbit_self r
  have hTO : ∀ t ∈ T0, ∀ y ∈ O, t y ∈ O := by
    rintro t ht _ ⟨q, rfl⟩
    have htS : t ∈ S := T0_le_S ht
    have htQ : (⟨t, htS⟩ : ↥S) ∈ Q₀ := hT ht
    exact ⟨⟨⟨t, htS⟩, htQ⟩ * q, rfl⟩
  have hfill : ∀ (D : Finset (Fin 42)) (d : Fin 42), (∀ y ∈ D, ∃ t ∈ T0, t d = y) → d ∈ D →
      (∃ y ∈ O, y ∈ D) → ∀ y ∈ D, y ∈ O := by
    rintro D d hD - ⟨a, ha, haD⟩ y hy
    obtain ⟨ta, hta, rfl⟩ := hD a haD
    obtain ⟨ty, hty, rfl⟩ := hD y hy
    have := hTO (ty * ta⁻¹) (T0.mul_mem hty (T0.inv_mem hta)) _ ha
    simpa using this
  have hdvd : O.ncard ∣ 960 := by
    rw [← index_stabilizer, ← hQ]
    exact Subgroup.index_dvd_card _
  intro x hx
  by_contra hne
  have hxH := hSH _ (x : ↥S).2
  have hxC : ((x : ↥S) : Equiv.Perm (Fin 42)) r ∈ C := by
    rcases (hH _).1 hxH with h | h | h
    · exact absurd (Finset.mem_insert.2 (Or.inl h)) hne
    · exact absurd (Finset.mem_insert.2 (Or.inr h)) hne
    · exact h
  have hCO := hfill C c hC hc ⟨_, ⟨⟨x, hx⟩, rfl⟩, hxC⟩
  by_cases hBO : ∃ y ∈ O, y ∈ B
  · have hBO' := hfill B b hB hb hBO
    have hOe : O = ↑H := by
      ext y
      refine ⟨hO y, fun hy => ?_⟩
      rcases (hH y).1 hy with rfl | h | h
      · exact hrO
      · exact hBO' y h
      · exact hCO y h
    rw [hOe, Set.ncard_coe_finset, hHc] at hdvd
    norm_num at hdvd
  · push Not at hBO
    have hOe : O = ↑(insert r C) := by
      ext y
      refine ⟨fun hy => ?_, fun hy => ?_⟩
      · rcases (hH y).1 (hO y hy) with h | h | h
        · exact Finset.mem_insert.2 (Or.inl h)
        · exact absurd h (hBO y hy)
        · exact Finset.mem_insert.2 (Or.inr h)
      · rcases Finset.mem_insert.1 hy with rfl | h
        · exact hrO
        · exact hCO y h
    rw [hOe, Set.ncard_coe_finset, hCc] at hdvd
    norm_num at hdvd

@[expose] def ptB : Finset (Fin 42) := {5, 10, 15, 20}

@[expose] def ptC : Finset (Fin 42) := {0, 1, 3, 4, 6, 7, 8, 9, 11, 12, 13, 14, 16, 17, 18, 19}

@[expose] def lnB : Finset (Fin 42) := {26, 31, 36, 41}

@[expose] def lnC : Finset (Fin 42) :=
  {21, 22, 24, 25, 27, 28, 29, 30, 32, 33, 34, 35, 37, 38, 39, 40}

theorem apply_two_mem {Q₀ : Subgroup ↥S} (hQ : Nat.card Q₀ = 960) (hT : T0.subgroupOf S ≤ Q₀) :
    ∀ x ∈ Q₀, ((x : ↥S) : Equiv.Perm (Fin 42)) 2 ∈ insert 2 ptB := by
  have hT0 := tree_ok
  refine apply_mem_of_orbit (r := 2) (b := 5) (c := 0) (H := pts) (B := ptB) (C := ptC) hQ hT
    (by decide) (by decide) (by decide) (by decide) (by decide) ?_ ?_ (by decide) ?_ (by decide)
  · intro x hx
    simpa [pts] using apply_lt_of_mem hx (i := 2) (by norm_num)
  · intro y hy
    exact exists_of_cover (exists_T0_of_tree 5 hT0.2.2.2.2.1) (by revert y; decide)
  · intro y hy
    exact exists_of_cover (exists_T0_of_tree 0 hT0.2.2.1) (by revert y; decide)

theorem apply_tt_mem {Q₀ : Subgroup ↥S} (hQ : Nat.card Q₀ = 960) (hT : T0.subgroupOf S ≤ Q₀) :
    ∀ x ∈ Q₀, ((x : ↥S) : Equiv.Perm (Fin 42)) 23 ∈ insert 23 lnB := by
  have hT0 := tree_ok
  refine apply_mem_of_orbit (r := 23) (b := 26) (c := 21) (H := lns) (B := lnB) (C := lnC) hQ hT
    (by decide) (by decide) (by decide) (by decide) (by decide) ?_ ?_ (by decide) ?_ (by decide)
  · intro x hx
    simpa [lns] using le_apply_of_mem hx (i := 23) (by norm_num)
  · intro y hy
    exact exists_of_cover (exists_T0_of_tree 26 hT0.2.2.2.2.2) (by revert y; decide)
  · intro y hy
    exact exists_of_cover (exists_T0_of_tree 21 hT0.2.2.2.1) (by revert y; decide)

theorem le_stab_of_le {Q₀ : Subgroup ↥S} (hQ : Nat.card Q₀ = 960) (hT : T0.subgroupOf S ≤ Q₀) :
    Q₀ ≤ stabilizer ↥S (2 : Fin 42) ∨ Q₀ ≤ stabilizer ↥S (23 : Fin 42) := by
  rw [← SubgroupClass.subset_union]
  intro x hx
  have h2 := apply_two_mem hQ hT x hx
  have h23 := apply_tt_mem hQ hT x hx
  have hf := (inv42_of_mem (x : ↥S).2).2.2 (2, 23) (by decide)
  simp only at hf
  rw [show (2 : ℕ) = ((2 : Fin 42) : ℕ) from rfl, show (23 : ℕ) = ((23 : Fin 42) : ℕ) from rfl,
    ap_fin, ap_fin] at hf
  have key : ∀ q ∈ insert (2 : Fin 42) ptB, ∀ m ∈ insert (23 : Fin 42) lnB,
      ((q : ℕ), (m : ℕ)) ∈ flagL → q = 2 ∨ m = 23 := by decide
  rcases key _ h2 _ h23 hf with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem exists_conj_eq_stab
    (Q : Subgroup ↥S) (hQ : Nat.card Q = 960) :
    ∃ g : ↥S, Q = MulAut.conj g • stabilizer ↥S (2 : Fin 42) ∨
      Q = MulAut.conj g • stabilizer ↥S (23 : Fin 42) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥Q) := inferInstance
  set T' : Subgroup ↥S := (T : Subgroup ↥Q).map Q.subtype with hT'
  have hT'c : Nat.card T' = 2 ^ (Nat.card ↥S).factorization 2 := by
    rw [hT', Subgroup.card_map_of_injective Q.subtype_injective, Sylow.card_eq_multiplicity, hQ,
      card_S, factorization_960, factorization_20160']
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥S sylowT0 (Sylow.ofCard T' hT'c)
  have hgT : MulAut.conj g • T0.subgroupOf S = T' := by
    have h1 := congrArg (fun P : Sylow 2 ↥S => (P : Subgroup ↥S)) hg
    simp only [Sylow.coe_subgroup_smul, coe_sylowT0, Sylow.coe_ofCard] at h1
    exact h1
  set Q₀ := MulAut.conj g⁻¹ • Q with hQ₀
  have hTQ : T0.subgroupOf S ≤ Q₀ := by
    intro t ht
    have h1 : MulAut.conj g • t ∈ T' := hgT ▸ Subgroup.smul_mem_pointwise_smul t _ _ ht
    obtain ⟨q, -, hq⟩ := h1
    rw [hQ₀, Subgroup.mem_smul_pointwise_iff_exists]
    refine ⟨MulAut.conj g • t, hq ▸ q.2, ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
  have hQ0 : Nat.card Q₀ = 960 := by
    rw [hQ₀, ← hQ]
    exact Set.natCard_smul_set _ (Q : Set ↥S)
  have hback : ∀ K : Subgroup ↥S, Q₀ = K → Q = MulAut.conj g • K := by
    rintro K rfl
    rw [hQ₀, smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  refine ⟨g, ?_⟩
  rcases le_stab_of_le hQ0 hTQ with h | h
  · exact Or.inl (hback _ (Subgroup.eq_of_le_of_card_ge h (by rw [card_stab_two, hQ0])))
  · exact Or.inr (hback _ (Subgroup.eq_of_le_of_card_ge h (by rw [card_stab_tt, hQ0])))

end CFSG.Quasithin.H.L34Cov
