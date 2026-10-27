module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelDefs

public section

namespace CFSG.StandardType

namespace E6Dep

@[expose] def cenCode : List ℕ := [1, 3, 4, 9, 12, 13, 27, 32, 34, 36, 39, 40, 46, 47, 50, 81, 86, 88, 95, 96, 98, 102, 103, 106, 122, 123, 125, 126, 132, 134, 144, 147, 148, 156, 157, 160]

@[expose] def cen (i : ℕ) : Vec6 := fun j => (((cenCode.getD i 0) / 3 ^ (j : ℕ) % 3 : ℕ) : ZMod 3)

@[expose] def cjTab : List (List ℕ) :=
  [[0, 2, 1, 3, 5, 4, 6, 7, 8, 9, 11, 10, 13, 12, 14, 15, 16, 17, 18, 20, 19, 22, 21, 23, 24, 26, 25, 27, 29, 28, 30, 32, 31, 34, 33, 35],
   [2, 1, 0, 4, 3, 5, 6, 7, 8, 10, 9, 11, 12, 14, 13, 15, 16, 17, 20, 19, 18, 21, 23, 22, 26, 25, 24, 28, 27, 29, 31, 30, 32, 33, 35, 34],
   [1, 0, 2, 5, 4, 3, 6, 7, 8, 11, 10, 9, 14, 13, 12, 15, 16, 17, 19, 18, 20, 23, 22, 21, 25, 24, 26, 29, 28, 27, 32, 31, 30, 35, 34, 33],
   [0, 4, 5, 3, 1, 2, 9, 14, 8, 6, 10, 11, 12, 13, 7, 15, 18, 23, 16, 19, 20, 21, 22, 17, 24, 28, 29, 27, 25, 26, 30, 33, 34, 31, 32, 35],
   [5, 3, 2, 1, 4, 0, 10, 13, 8, 9, 6, 11, 12, 7, 14, 15, 20, 22, 18, 19, 16, 21, 17, 23, 29, 27, 26, 25, 28, 24, 33, 31, 35, 30, 34, 32],
   [4, 1, 3, 2, 0, 5, 11, 12, 8, 9, 10, 6, 7, 13, 14, 15, 19, 21, 18, 16, 20, 17, 22, 23, 28, 25, 27, 26, 24, 29, 34, 35, 32, 33, 30, 31],
   [0, 1, 2, 9, 10, 11, 6, 8, 7, 3, 4, 5, 12, 13, 14, 15, 16, 17, 24, 25, 26, 33, 34, 35, 18, 19, 20, 27, 28, 29, 30, 31, 32, 21, 22, 23],
   [0, 1, 2, 14, 13, 12, 8, 7, 6, 9, 10, 11, 5, 4, 3, 15, 16, 17, 30, 32, 31, 29, 28, 27, 24, 25, 26, 23, 22, 21, 18, 20, 19, 33, 34, 35],
   [0, 1, 2, 3, 4, 5, 7, 6, 8, 14, 13, 12, 11, 10, 9, 15, 16, 17, 18, 19, 20, 21, 22, 23, 30, 32, 31, 35, 34, 33, 24, 26, 25, 29, 28, 27],
   [0, 10, 11, 6, 4, 5, 3, 7, 14, 9, 1, 2, 12, 13, 8, 15, 24, 35, 18, 28, 29, 31, 32, 23, 16, 25, 26, 27, 19, 20, 30, 21, 22, 33, 34, 17],
   [11, 9, 2, 3, 6, 5, 4, 7, 13, 1, 10, 0, 12, 8, 14, 15, 26, 34, 29, 27, 20, 30, 22, 32, 24, 25, 16, 19, 28, 18, 21, 31, 23, 33, 17, 35],
   [10, 1, 9, 3, 4, 6, 5, 7, 12, 2, 0, 11, 8, 13, 14, 15, 25, 33, 28, 19, 27, 21, 30, 31, 24, 16, 26, 20, 18, 29, 22, 23, 32, 17, 34, 35],
   [13, 1, 14, 3, 4, 7, 6, 5, 11, 9, 10, 8, 12, 0, 2, 15, 32, 29, 34, 19, 35, 21, 24, 26, 22, 25, 23, 27, 28, 17, 30, 31, 16, 33, 18, 20],
   [12, 14, 2, 3, 7, 5, 6, 4, 10, 9, 8, 11, 0, 13, 1, 15, 31, 28, 33, 35, 20, 24, 22, 25, 21, 23, 26, 27, 17, 29, 30, 16, 32, 18, 34, 19],
   [0, 13, 12, 7, 4, 5, 6, 3, 9, 8, 10, 11, 2, 1, 14, 15, 30, 27, 18, 34, 33, 26, 25, 23, 24, 22, 21, 17, 28, 29, 16, 31, 32, 20, 19, 35],
   [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 16, 23, 21, 22, 19, 20, 18, 35, 33, 34, 30, 31, 32, 27, 28, 29, 25, 26, 24],
   [0, 1, 2, 18, 20, 19, 6, 7, 8, 24, 26, 25, 32, 31, 30, 17, 16, 15, 3, 5, 4, 21, 22, 23, 9, 11, 10, 27, 28, 29, 14, 13, 12, 33, 34, 35],
   [0, 1, 2, 23, 22, 21, 6, 7, 8, 35, 34, 33, 29, 28, 27, 16, 15, 17, 18, 19, 20, 5, 4, 3, 24, 25, 26, 14, 13, 12, 30, 31, 32, 11, 10, 9],
   [0, 20, 19, 16, 4, 5, 24, 30, 8, 9, 29, 28, 34, 33, 14, 23, 3, 17, 18, 2, 1, 21, 22, 15, 6, 25, 26, 27, 11, 10, 7, 31, 32, 13, 12, 35],
   [20, 1, 18, 3, 4, 16, 25, 32, 8, 28, 27, 11, 12, 35, 34, 21, 5, 17, 2, 19, 0, 15, 22, 23, 24, 6, 26, 10, 9, 29, 30, 31, 7, 33, 14, 13],
   [19, 18, 2, 3, 16, 5, 26, 31, 8, 29, 10, 27, 35, 13, 33, 22, 4, 17, 1, 0, 20, 21, 15, 23, 24, 25, 6, 11, 28, 9, 30, 7, 32, 14, 34, 12],
   [22, 1, 23, 3, 4, 17, 33, 29, 8, 31, 30, 11, 12, 24, 26, 19, 16, 5, 18, 15, 20, 21, 0, 2, 13, 25, 14, 27, 28, 7, 10, 9, 32, 6, 34, 35],
   [21, 23, 2, 3, 17, 5, 34, 28, 8, 32, 10, 30, 24, 13, 25, 20, 16, 4, 18, 19, 15, 0, 22, 1, 12, 14, 26, 27, 7, 29, 11, 31, 9, 33, 6, 35],
   [0, 22, 21, 17, 4, 5, 35, 27, 8, 9, 32, 31, 26, 25, 14, 18, 16, 3, 15, 19, 20, 2, 1, 23, 24, 13, 12, 7, 28, 29, 30, 11, 10, 33, 34, 6],
   [0, 26, 25, 3, 29, 28, 18, 7, 30, 16, 10, 11, 22, 21, 14, 35, 9, 17, 6, 19, 20, 13, 12, 23, 24, 2, 1, 27, 5, 4, 8, 31, 32, 33, 34, 15],
   [26, 1, 24, 28, 27, 5, 19, 7, 32, 9, 10, 16, 12, 23, 22, 33, 11, 17, 18, 6, 20, 21, 14, 13, 2, 25, 0, 4, 3, 29, 30, 31, 8, 15, 34, 35],
   [25, 24, 2, 29, 4, 27, 20, 7, 31, 9, 16, 11, 23, 13, 21, 34, 10, 17, 18, 19, 6, 14, 22, 12, 1, 0, 26, 5, 28, 3, 30, 8, 32, 33, 15, 35],
   [0, 28, 29, 3, 25, 26, 6, 23, 35, 9, 19, 20, 12, 13, 17, 30, 16, 14, 18, 10, 11, 21, 22, 7, 24, 4, 5, 27, 1, 2, 15, 31, 32, 33, 34, 8],
   [29, 27, 2, 25, 4, 24, 6, 22, 34, 19, 10, 18, 12, 17, 14, 31, 16, 13, 11, 9, 20, 21, 7, 23, 5, 3, 26, 1, 28, 0, 30, 15, 32, 33, 8, 35],
   [28, 1, 27, 26, 24, 5, 6, 21, 33, 20, 18, 11, 17, 13, 14, 32, 16, 12, 10, 19, 9, 7, 22, 23, 4, 25, 3, 2, 0, 29, 30, 31, 15, 8, 34, 35],
   [0, 31, 32, 3, 33, 34, 6, 18, 24, 9, 21, 22, 12, 13, 16, 27, 14, 17, 7, 19, 20, 10, 11, 23, 8, 25, 26, 15, 28, 29, 30, 1, 2, 4, 5, 35],
   [32, 30, 2, 33, 4, 35, 6, 20, 26, 21, 10, 23, 12, 16, 14, 28, 13, 17, 18, 19, 7, 9, 22, 11, 24, 25, 8, 27, 15, 29, 1, 31, 0, 3, 34, 5],
   [31, 1, 30, 34, 35, 5, 6, 19, 25, 22, 23, 11, 16, 13, 14, 29, 12, 17, 18, 7, 20, 21, 9, 10, 24, 8, 26, 27, 28, 15, 2, 0, 32, 33, 3, 4],
   [34, 1, 35, 31, 30, 5, 21, 7, 29, 9, 10, 17, 12, 18, 20, 25, 16, 11, 13, 19, 14, 6, 22, 23, 24, 15, 26, 27, 28, 8, 4, 3, 32, 33, 0, 2],
   [33, 35, 2, 32, 4, 30, 22, 7, 28, 9, 17, 11, 18, 13, 19, 26, 16, 10, 12, 14, 20, 21, 6, 23, 24, 25, 15, 27, 8, 29, 5, 31, 3, 0, 34, 1],
   [0, 34, 33, 3, 32, 31, 23, 7, 27, 17, 10, 11, 20, 19, 14, 24, 16, 9, 18, 13, 12, 21, 22, 6, 15, 25, 26, 8, 28, 29, 30, 5, 4, 2, 1, 35]]

@[expose] def cjN (a b : ℕ) : ℕ := (cjTab.getD a []).getD b 0

@[expose] def CjClosed (I : Finset ℕ) : Prop := ∀ a ∈ I, ∀ b ∈ I, cjN a b ∈ I

@[expose] def CjGen (X : Finset ℕ) : Prop :=
  ∀ I : Finset ℕ, I ⊆ Finset.range 36 → CjClosed I → X ⊆ I → I = Finset.range 36

@[expose] def zset (v : Vec6) : Finset ℕ := (Finset.range 36).filter fun i => bil6 (cen i) v = 0

@[expose] def fix1 (c : ℕ) : Finset ℕ := zset (cen c)

private def maxl : List ℕ := [36042188808, 1071804607, 33126138825, 18833482272, 48659049108, 41632975985, 61071064839, 60247215751, 1100611849, 4831897698, 38992627728, 35593372617, 12435417050, 5705441348, 67660549759, 8623527586, 12445161754, 41047113201, 20002709572, 13384619682, 19668379092, 49045297940, 45427436140, 23292062316, 37082121248, 8472268423, 6593855553, 3792310338, 12250027610, 68702732607, 56458012826, 55261305314, 17459904788, 22879020332, 56274262298, 10008138256, 67647664319, 49051117012, 35534537345, 41043772209, 2660634, 32373361801, 7635599815, 52112197762, 20053906516, 32369881673, 22872415212, 229831, 19889932304, 55334803106, 34376567945, 45421221036, 17247021716, 1058868863, 10893136904, 61083812295, 45847043052, 2415973460, 23298299052, 19378865284, 33127120137, 19497488912, 34500575497, 8455974983, 13090693664, 43289478276, 13289721922, 13179569184, 21628987400, 60263559239, 45840409900, 4332060962, 2219704596, 36247257153, 19674225428, 20060383892, 41632379569, 13458184674, 13375006818, 1208005193, 48665547860, 56284047322, 27672329713, 55344457826, 36349555273, 12261517466, 8700721, 55250249506, 7648411399, 36346088585, 35592387849, 56469460570, 16744767, 25929253505, 27087123121, 12969445506, 13469280034, 65535, 27086539889, 5285164, 27675673393, 9139978530, 35738620936]

private def closedM (N : ℕ) : Bool :=
  (List.range 36).all fun a => !N.testBit a ||
    (List.range 36).all fun b => !N.testBit b || N.testBit (cjN a b)

private theorem maxl_fact : ∀ N ∈ maxl, closedM N = true ∧
    (List.range 36).any (fun i => !N.testBit i) = true := by decide +kernel

private theorem cjN_lt : ∀ a < 36, ∀ b < 36, cjN a b < 36 := by decide +kernel

private def maskOfList (l : List ℕ) : ℕ := l.foldr (fun i acc => 2 ^ i ||| acc) 0

private def zmask (v : Vec6) : ℕ :=
  maskOfList ((List.range 36).filter fun i => bil6 (cen i) v = 0)

private theorem norm2_cert : ∀ v : Vec6, v 5 = 0 → norm6 v = 2 → ∀ r < 36, ∃ N ∈ maxl,
    ((zmask v ||| 2 ^ r) &&& N) = (zmask v ||| 2 ^ r) := by decide +kernel

private def U0l : List ℕ := [3, 6, 7, 8, 9, 14, 15, 16, 17, 18, 23, 24, 27, 30, 35]

private theorem fix1_mem : ∀ i < 36, (bil6 (cen i) (cen 0) = 0 ↔ i ∈ U0l) := by decide +kernel

private def cj15 : List (List ℕ) :=
  [[0, 4, 5, 3, 1, 2, 6, 9, 10, 7, 8, 11, 12, 13, 14],
   [4, 1, 3, 2, 0, 5, 6, 7, 8, 11, 14, 9, 12, 13, 10],
   [5, 3, 2, 1, 4, 0, 6, 7, 8, 13, 12, 11, 10, 9, 14],
   [0, 2, 1, 3, 5, 4, 6, 7, 8, 9, 10, 13, 14, 11, 12],
   [1, 0, 2, 5, 4, 3, 6, 11, 14, 9, 10, 7, 12, 13, 8],
   [2, 1, 0, 4, 3, 5, 6, 13, 12, 9, 10, 11, 8, 7, 14],
   [0, 1, 2, 3, 4, 5, 6, 8, 7, 10, 9, 14, 13, 12, 11],
   [9, 1, 2, 3, 11, 13, 8, 7, 6, 0, 10, 4, 12, 5, 14],
   [10, 1, 2, 3, 14, 12, 7, 6, 8, 9, 0, 11, 5, 13, 4],
   [7, 11, 13, 3, 4, 5, 10, 0, 8, 9, 6, 1, 12, 2, 14],
   [8, 14, 12, 3, 4, 5, 9, 7, 0, 6, 10, 11, 2, 13, 1],
   [0, 9, 2, 13, 7, 5, 14, 4, 8, 1, 10, 11, 12, 3, 6],
   [0, 1, 10, 14, 4, 8, 13, 7, 5, 9, 2, 11, 12, 6, 3],
   [0, 1, 9, 11, 4, 7, 12, 5, 8, 2, 10, 3, 6, 13, 14],
   [0, 10, 2, 12, 8, 5, 11, 7, 4, 9, 1, 6, 3, 13, 14]]

private def cj15g (a b : ℕ) : ℕ := (cj15.getD a []).getD b 0

private theorem cj15_fact : ∀ a < 15, ∀ b < 15, cj15g a b < 15 ∧
    cjN (U0l.getD a 0) (U0l.getD b 0) = U0l.getD (cj15g a b) 0 := by decide +kernel

private def closed15 (m : ℕ) : Bool :=
  (List.range 15).all fun a => !m.testBit a ||
    (List.range 15).all fun b => !m.testBit b || m.testBit (cj15g a b)

private def emb (m : ℕ) : ℕ :=
  (List.range 15).foldl
    (fun acc a => if m.testBit a then acc ||| 2 ^ (U0l.getD a 0) else acc) 0

private def cert (S : ℕ) : Bool :=
  (List.range 36).all fun r => maxl.any fun N =>
    ((S ||| 2 ^ r) &&& N) == (S ||| 2 ^ r)

private def baseCheck : Bool :=
  (List.range 32768).all fun m => !closed15 m || m == 32767 || cert (emb m)

private theorem baseCheck_true : baseCheck = true := by decide +kernel

private theorem maskOfList_testBit (l : List ℕ) (i : ℕ) :
    (maskOfList l).testBit i = true ↔ i ∈ l := by
  induction l with
  | nil => simp [maskOfList]
  | cons a l ih =>
      change (2 ^ a ||| maskOfList l).testBit i = true ↔ i ∈ a :: l
      rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq, ih,
        List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr h

private theorem mem_zset_iff (v : Vec6) (i : ℕ) :
    i ∈ zset v ↔ i < 36 ∧ (zmask v).testBit i = true := by
  simp [zset, zmask, maskOfList_testBit, Finset.mem_filter, Finset.mem_range, List.mem_filter,
    List.mem_range]

private def ofMask (N : ℕ) : Finset ℕ :=
  (Finset.range 36).filter (fun i => N.testBit i = true)

private theorem mem_ofMask (N i : ℕ) :
    i ∈ ofMask N ↔ i < 36 ∧ N.testBit i = true := by
  simp [ofMask, Finset.mem_filter, Finset.mem_range]

private theorem or_right_of_not_true {b c : Bool} (h : (!b || c) = true) (hb : b = true) :
    c = true := by
  rw [hb] at h
  simpa using h

private theorem closedM_closed {N : ℕ} (h : closedM N = true) : CjClosed (ofMask N) := by
  intro a ha b hb
  rw [mem_ofMask] at ha hb ⊢
  obtain ⟨ha36, hNa⟩ := ha
  obtain ⟨hb36, hNb⟩ := hb
  refine ⟨cjN_lt a ha36 b hb36, ?_⟩
  unfold closedM at h
  rw [List.all_eq_true] at h
  have hall := h a (List.mem_range.mpr ha36)
  have hinner := or_right_of_not_true hall hNa
  rw [List.all_eq_true] at hinner
  have hall2 := hinner b (List.mem_range.mpr hb36)
  exact or_right_of_not_true hall2 hNb

private theorem ofMask_ne_range {N : ℕ} (hN : N ∈ maxl) : ofMask N ≠ Finset.range 36 := by
  intro hEq
  obtain ⟨-, hany⟩ := maxl_fact N hN
  rw [List.any_eq_true] at hany
  obtain ⟨i, hi, hibit⟩ := hany
  have hi36 : i < 36 := List.mem_range.mp hi
  have hif : N.testBit i = false := by
    cases h : N.testBit i
    · rfl
    · rw [h] at hibit
      exact absurd hibit Bool.false_ne_true
  have : i ∈ ofMask N := by rw [hEq]; exact Finset.mem_range.mpr hi36
  rw [mem_ofMask] at this
  rw [this.2] at hif
  exact absurd hif (by decide)

private theorem not_gen_of_mask {N : ℕ} (hN : N ∈ maxl) {X : Finset ℕ}
    (hX : ∀ i ∈ X, i < 36 ∧ N.testBit i = true) : ¬ CjGen X := by
  intro hgen
  obtain ⟨hclosed, -⟩ := maxl_fact N hN
  have hc : CjClosed (ofMask N) := closedM_closed hclosed
  have hsub : X ⊆ ofMask N := by
    intro i hi
    rw [mem_ofMask]
    exact hX i hi
  have hrange : ofMask N ⊆ Finset.range 36 := by
    intro i hi
    rw [mem_ofMask] at hi
    exact Finset.mem_range.mpr hi.1
  exact ofMask_ne_range hN (hgen (ofMask N) hrange hc hsub)

private theorem testBit_of_and_eq {a N i : ℕ} (h : a &&& N = a) (ha : a.testBit i = true) :
    N.testBit i = true := by
  have hb := congrArg (fun x => x.testBit i) h
  rw [Nat.testBit_and] at hb
  rw [ha] at hb
  simpa using hb

private def stepM (m : ℕ) : ℕ → ℕ → ℕ :=
  fun acc a => if m.testBit a then acc ||| 2 ^ (U0l.getD a 0) else acc

private theorem testBit_foldl_stepM_mono (m i : ℕ) :
    ∀ (l : List ℕ) (acc : ℕ), acc.testBit i = true →
      (l.foldl (stepM m) acc).testBit i = true := by
  intro l
  induction l with
  | nil => intro acc h; simpa using h
  | cons a l ih =>
      intro acc h
      rw [List.foldl_cons]
      apply ih
      by_cases hma : m.testBit a = true
      · rw [stepM, if_pos hma]
        simp [Nat.testBit_or, h]
      · rw [stepM, if_neg hma]
        exact h

private theorem testBit_foldl_stepM_of_mem (m i : ℕ) (l : List ℕ) (a : ℕ)
    (ha : a ∈ l) (hma : m.testBit a = true) (hUi : U0l.getD a 0 = i) :
    ∀ acc, (l.foldl (stepM m) acc).testBit i = true := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
  intro acc
  rw [List.foldl_append, List.foldl_cons]
  apply testBit_foldl_stepM_mono
  rw [stepM, if_pos hma]
  rw [Nat.testBit_or, Bool.or_eq_true]
  right
  rw [Nat.testBit_two_pow, hUi, decide_eq_true_eq]

private theorem emb_testBit (m a : ℕ) (ha : a < 15) (hma : m.testBit a = true) :
    (emb m).testBit (U0l.getD a 0) = true := by
  unfold emb
  exact testBit_foldl_stepM_of_mem m (U0l.getD a 0) (List.range 15) a
    (List.mem_range.mpr ha) hma rfl 0

private theorem U0l_length : U0l.length = 15 := by decide

private theorem getD_eq_getElem_of_lt {l : List ℕ} {a : ℕ} (h : a < l.length) (d : ℕ) :
    l.getD a d = l[a] := by
  change (l[a]?).getD d = l[a]
  rw [List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩]
  rfl

private theorem mem_U0l_exists (i : ℕ) : i ∈ U0l ↔ ∃ a < 15, U0l.getD a 0 = i := by
  constructor
  · intro hi
    obtain ⟨a, ha, heq⟩ := List.mem_iff_getElem.mp hi
    have hget : U0l.getD a 0 = i := by rw [getD_eq_getElem_of_lt ha 0]; exact heq
    have ha15 : a < 15 := by rw [U0l_length] at ha; exact ha
    exact ⟨a, ha15, hget⟩
  · rintro ⟨a, ha, rfl⟩
    have hlt : a < U0l.length := by rwa [U0l_length]
    rw [getD_eq_getElem_of_lt hlt 0]
    exact List.getElem_mem hlt

private theorem mem_fix1_iff (i : ℕ) : i ∈ fix1 0 ↔ i < 36 ∧ i ∈ U0l := by
  constructor
  · intro hi
    rw [fix1, zset, Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨hi.1, (fix1_mem i hi.1).mp hi.2⟩
  · rintro ⟨hi36, hiU⟩
    rw [fix1, zset, Finset.mem_filter, Finset.mem_range]
    exact ⟨hi36, (fix1_mem i hi36).mpr hiU⟩

private def mOf (I : Finset ℕ) : ℕ :=
  maskOfList ((List.range 15).filter (fun a => decide (U0l.getD a 0 ∈ I)))

private theorem mOf_testBit (I : Finset ℕ) (a : ℕ) :
    (mOf I).testBit a = true ↔ a < 15 ∧ U0l.getD a 0 ∈ I := by
  simp [mOf, maskOfList_testBit, List.mem_filter, List.mem_range]

private theorem mOf_lt (I : Finset ℕ) : mOf I < 2 ^ 15 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have hnot : ¬ ((mOf I).testBit i = true) := by
    intro h
    exact absurd ((mOf_testBit I i).mp h).1 (by omega)
  cases hb : (mOf I).testBit i
  · rfl
  · exact absurd hb hnot

private theorem closed15_mOf {I : Finset ℕ} (hcl : CjClosed I) :
    closed15 (mOf I) = true := by
  unfold closed15
  rw [List.all_eq_true]
  intro a ha
  rw [List.mem_range] at ha
  cases hma : (mOf I).testBit a
  · simp [hma]
  · simp only [hma, Bool.not_true, Bool.false_or]
    rw [List.all_eq_true]
    intro b hb
    rw [List.mem_range] at hb
    have hma' := (mOf_testBit I a).mp hma
    cases hmb : (mOf I).testBit b
    · simp [hmb]
    · simp only [hmb, Bool.not_true, Bool.false_or]
      have hmb' := (mOf_testBit I b).mp hmb
      obtain ⟨hclt, hcj⟩ := cj15_fact a hma'.1 b hmb'.1
      rw [mOf_testBit]
      exact ⟨hclt, by rw [← hcj]; exact hcl _ hma'.2 _ hmb'.2⟩

private theorem mOf_ne (I : Finset ℕ) (hI : I ⊆ fix1 0) (hne : I ≠ fix1 0) :
    mOf I ≠ 32767 := by
  intro hm
  apply hne
  apply Finset.Subset.antisymm hI
  intro i hi
  have hfix := (mem_fix1_iff i).mp hi
  obtain ⟨a, ha, hget⟩ := (mem_U0l_exists i).mp hfix.2
  have hbit : (mOf I).testBit a = true := by
    rw [hm]
    have h32767 : (32767 : ℕ).testBit a = true := by
      have h2 : (32767 : ℕ) = 2 ^ 15 - 1 := by norm_num
      rw [h2, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
      exact ha
    exact h32767
  have hmem : U0l.getD a 0 ∈ I := ((mOf_testBit I a).mp hbit).2
  rw [hget] at hmem
  exact hmem

theorem norm2_not_gen {v : Vec6} (hv5 : v 5 = 0) (hv : norm6 v = 2) {r : ℕ} (hr : r < 36) :
    ¬ CjGen (insert r (zset v)) := by
  obtain ⟨N, hN, hEq⟩ := norm2_cert v hv5 hv r hr
  apply not_gen_of_mask hN
  intro i hi
  rcases Finset.mem_insert.mp hi with rfl | hzi
  · refine ⟨hr, testBit_of_and_eq hEq ?_⟩
    rw [Nat.testBit_or, Bool.or_eq_true]
    exact Or.inr Nat.testBit_two_pow_self
  · have hz := (mem_zset_iff v i).mp hzi
    refine ⟨hz.1, testBit_of_and_eq hEq ?_⟩
    rw [Nat.testBit_or, Bool.or_eq_true]
    exact Or.inl hz.2

theorem base_not_gen {I : Finset ℕ} (hI : I ⊆ fix1 0) (hcl : CjClosed I) (hne : I ≠ fix1 0)
    {r : ℕ} (hr : r < 36) : ¬ CjGen (insert r I) := by
  have hm_lt : mOf I < 32768 := by
    have h := mOf_lt I
    norm_num at h
    exact h
  have hclosed : closed15 (mOf I) = true := closed15_mOf hcl
  have hmne : mOf I ≠ 32767 := mOf_ne I hI hne
  have hcert : cert (emb (mOf I)) = true := by
    have hall := (List.all_eq_true.mp baseCheck_true) (mOf I) (List.mem_range.mpr hm_lt)
    rw [hclosed] at hall
    simp only [Bool.not_true, Bool.false_or] at hall
    rw [Bool.or_eq_true] at hall
    rcases hall with h | h
    · rw [Nat.beq_eq_true_eq] at h
      exact absurd h hmne
    · exact h
  have hall2 := (List.all_eq_true.mp hcert) r (List.mem_range.mpr hr)
  obtain ⟨N, hN, hEqBeq⟩ := List.any_eq_true.mp hall2
  rw [Nat.beq_eq_true_eq] at hEqBeq
  apply not_gen_of_mask hN
  intro i hi
  rcases Finset.mem_insert.mp hi with rfl | hiI
  · refine ⟨hr, testBit_of_and_eq hEqBeq ?_⟩
    rw [Nat.testBit_or, Bool.or_eq_true]
    exact Or.inr Nat.testBit_two_pow_self
  · have hfix := (mem_fix1_iff i).mp (hI hiI)
    obtain ⟨a, ha15, hget⟩ := (mem_U0l_exists i).mp hfix.2
    have hma : (mOf I).testBit a = true := by
      rw [mOf_testBit]
      exact ⟨ha15, by rw [hget]; exact hiI⟩
    have hemb : (emb (mOf I)).testBit i = true := by
      rw [← hget]
      exact emb_testBit (mOf I) a ha15 hma
    refine ⟨hfix.1, testBit_of_and_eq hEqBeq ?_⟩
    rw [Nat.testBit_or, Bool.or_eq_true]
    exact Or.inl hemb

end E6Dep

end CFSG.StandardType

end
