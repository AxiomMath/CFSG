module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusInsideGrow

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

variable {m : Fin 6} {T : Chk.Tabs}

private abbrev rtRoot (hT : Chk.tabsOK m T = true) (u t : Root m) : Root m :=
  ⟨(T.rt[u.val]!)[t.val]!, tabsOK_rt_lt hT u t⟩

private theorem rtRoot_involutive (hT : Chk.tabsOK m T = true) {u : Root m}
    (hinv : ∀ t : Root m, (T.rt[u.val]!)[(T.rt[u.val]!)[t.val]!]! = t.val) (t : Root m) :
    rtRoot hT u (rtRoot hT u t) = t :=
  Fin.ext (hinv t)

private theorem mem_ofMask_imgN_rtRoot (hT : Chk.tabsOK m T = true) {u : Root m}
    (hinv : ∀ t : Root m, (T.rt[u.val]!)[(T.rt[u.val]!)[t.val]!]! = t.val) (n : ℕ)
    (t : Root m) :
    t ∈ ofMask m (Chk.imgN T (nroots m) u n) ↔ rtRoot hT u t ∈ ofMask m n := by
  rw [mem_ofMask_imgN]
  constructor
  · rintro ⟨s, hs, hst⟩
    have h1 : rtRoot hT u s = t := Fin.ext hst
    rw [← h1, rtRoot_involutive hT hinv s]
    exact hs
  · intro ht
    refine ⟨rtRoot hT u t, ht, ?_⟩
    exact congrArg Fin.val (rtRoot_involutive hT hinv t)

private theorem testBit_imgN (hT : Chk.tabsOK m T = true) {u : Root m}
    (hinv : ∀ t : Root m, (T.rt[u.val]!)[(T.rt[u.val]!)[t.val]!]! = t.val) (n : ℕ)
    (z : Root m) :
    (Chk.imgN T (nroots m) u n).testBit z.val = n.testBit (rtRoot hT u z).val := by
  apply Bool.eq_iff_iff.mpr
  rw [← mem_ofMask (t := z), mem_ofMask_imgN_rtRoot hT hinv, mem_ofMask (t := rtRoot hT u z)]

private theorem mem_cent_iff {c : Finset (Root m)} {w : V m} :
    w ∈ cent m c ↔ ∀ i ∈ c, root m i w = 0 := by
  simp only [cent, Submodule.mem_iInf, LinearMap.mem_ker]

private theorem eq_zero_of_eps_mul {ε x : ZMod 3} (hε : ε = 1 ∨ ε = -1) (h : ε * x = 0) :
    x = 0 := by
  rcases hε with rfl | rfl
  · simpa only [one_mul] using h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (by decide)
    · exact h' 

private theorem mem_cent_iff_imgN (hT : Chk.tabsOK m T = true) {u : Root m}
    (hinv : ∀ t : Root m, (T.rt[u.val]!)[(T.rt[u.val]!)[t.val]!]! = t.val) (n : ℕ)
    (w : V m) :
    w ∈ cent m (ofMask m (Chk.imgN T (nroots m) u n)) ↔
      reflection m u w ∈ cent m (ofMask m n) := by
  have hL : w ∈ cent m (ofMask m (Chk.imgN T (nroots m) u n)) ↔
      ∀ i ∈ ofMask m (Chk.imgN T (nroots m) u n), root m i w = 0 := mem_cent_iff
  have hR : reflection m u w ∈ cent m (ofMask m n) ↔
      ∀ i ∈ ofMask m n, root m i (reflection m u w) = 0 := mem_cent_iff
  rw [hL, hR]
  constructor
  · intro h s hs
    have hmem : rtRoot hT u s ∈ ofMask m (Chk.imgN T (nroots m) u n) := by
      rw [mem_ofMask_imgN_rtRoot hT hinv, rtRoot_involutive hT hinv s]
      exact hs
    obtain ⟨ε, hε, hroot⟩ := root_rt_eq hT u s
    have h1 : ε * root m s (reflection m u w) = 0 := by
      rw [← hroot w]
      exact h (rtRoot hT u s) hmem
    exact eq_zero_of_eps_mul hε h1
  · intro h t ht
    rw [mem_ofMask_imgN] at ht
    obtain ⟨s, hs, hst⟩ := ht
    have hst' : rtRoot hT u s = t := Fin.ext hst
    obtain ⟨ε, hε, hroot⟩ := root_rt_eq hT u s
    have h2 : root m t w = ε * root m s (reflection m u w) := by
      rw [← hst']
      exact hroot w
    rw [h2, h s hs, mul_zero]

private theorem vanish_cent_imgN (hT : Chk.tabsOK m T = true) {u : Root m}
    (hinv : ∀ t : Root m, (T.rt[u.val]!)[(T.rt[u.val]!)[t.val]!]! = t.val) (n : ℕ)
    (j : Root m) :
    Vanish m (cent m (ofMask m (Chk.imgN T (nroots m) u n))) j ↔
      Vanish m (cent m (ofMask m n)) (rtRoot hT u j) := by
  constructor
  · intro h w hw
    have hmem : reflection m u w ∈ cent m (ofMask m (Chk.imgN T (nroots m) u n)) := by
      refine (mem_cent_iff_imgN hT hinv n (reflection m u w)).mpr ?_
      have hww : reflection m u (reflection m u w) = w :=
        Module.involutive_reflection (root_coroot m u) w
      rw [hww]
      exact hw
    have h1 : root m j (reflection m u w) = 0 := h (reflection m u w) hmem
    obtain ⟨ε, hε, hroot⟩ := root_rt_eq hT u j
    have h2 : ε * root m j (reflection m u w) = 0 := by rw [h1, mul_zero]
    change root m ⟨(T.rt[u.val]!)[j.val]!, tabsOK_rt_lt hT u j⟩ w = 0
    rw [hroot w]
    exact h2
  · intro h w hw
    have hmem : reflection m u w ∈ cent m (ofMask m n) :=
      (mem_cent_iff_imgN hT hinv n w).mp hw
    have h1 : root m (rtRoot hT u j) (reflection m u w) = 0 := h (reflection m u w) hmem
    obtain ⟨ε, hε, hroot⟩ := root_rt_eq hT u (rtRoot hT u j)
    have h2 : root m j w = ε * root m (rtRoot hT u j) (reflection m u w) := by
      have h3 := hroot w
      exact (congrArg (fun r => root m r w) (rtRoot_involutive hT hinv j)).symm.trans h3
    rw [h2, h1, mul_zero]

private theorem testBit_fold_grow (r c S t : ℕ) :
    (Nat.fold r (fun s _ acc => if S.testBit s then acc ||| (T.adj[s]! &&& c) else acc)
        S).testBit t = true ↔
      S.testBit t = true ∨ ∃ s, s < r ∧ S.testBit s = true ∧
        (T.adj[s]!).testBit t = true ∧ c.testBit t = true := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.fold_succ]
    by_cases hS : S.testBit r = true
    · rw [if_pos hS, Nat.testBit_lor, Nat.testBit_and, Bool.or_eq_true_iff,
        Bool.and_eq_true_iff, ih]
      constructor
      · rintro (⟨hacc | ⟨s, hs, hSs, hadj, hc⟩⟩ | ⟨hadj, hc⟩)
        · exact Or.inl hacc
        · exact Or.inr ⟨s, by omega, hSs, hadj, hc⟩
        · exact Or.inr ⟨r, by omega, hS, hadj, hc⟩
      · rintro (h | ⟨s, hs, hSs, hadj, hc⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs' | rfl
          · exact Or.inl (Or.inr ⟨s, hs', hSs, hadj, hc⟩)
          · exact Or.inr ⟨hadj, hc⟩
    · rw [if_neg hS, ih]
      constructor
      · rintro (h | ⟨s, hs, hSs, hadj, hc⟩)
        · exact Or.inl h
        · exact Or.inr ⟨s, by omega, hSs, hadj, hc⟩
      · rintro (h | ⟨s, hs, hSs, hadj, hc⟩)
        · exact Or.inl h
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs' | rfl
          · exact Or.inr ⟨s, hs', hSs, hadj, hc⟩
          · exact absurd hSs hS

private theorem testBit_growN (c S t : ℕ) :
    (Chk.growN T (nroots m) c S).testBit t = true ↔
      S.testBit t = true ∨ ∃ s : Root m, S.testBit s.val = true ∧
        (T.adj[s.val]!).testBit t = true ∧ c.testBit t = true := by
  rw [Chk.growN, testBit_fold_grow]
  constructor
  · rintro (h | ⟨s, hs, hSs, hadj, hc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨s, hs⟩, hSs, hadj, hc⟩
  · rintro (h | ⟨⟨s, hs⟩, hSs, hadj, hc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨s, hs, hSs, hadj, hc⟩

private theorem growN_lt_nroots (hT : Chk.tabsOK m T = true) {c S : ℕ}
    (hS : S < 2 ^ nroots m) : Chk.growN T (nroots m) c S < 2 ^ nroots m := by
  apply Nat.lt_pow_two_of_testBit
  intro t ht
  have hpow : 2 ^ nroots m ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
  have hSfalse : S.testBit t = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hS hpow)
  cases hb : (Chk.growN T (nroots m) c S).testBit t with
  | false => rfl
  | true =>
      rw [testBit_growN] at hb
      rcases hb with h | ⟨s, hSs, hadj, hc⟩
      · rw [hSfalse] at h
        exact absurd h (by simp)
      · obtain ⟨hlt, -⟩ := (tabsOK_adj hT s t).mp hadj
        omega

private theorem closN_imgN (hT : Chk.tabsOK m T = true) {u : Root m}
    (hinv : ∀ t : Root m, (T.rt[u.val]!)[(T.rt[u.val]!)[t.val]!]! = t.val)
    {c : ℕ} (hc : c < 2 ^ nroots m) :
    Chk.closN T (dim m) (nroots m) (Chk.imgN T (nroots m) u c) =
      Chk.imgN T (nroots m) u (Chk.closN T (dim m) (nroots m) c) := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < nroots m
  · apply Bool.eq_iff_iff.mpr
    have h1 : (Chk.closN T (dim m) (nroots m) (Chk.imgN T (nroots m) u c)).testBit t = true ↔
        Vanish m (cent m (ofMask m (Chk.imgN T (nroots m) u c))) ⟨t, ht⟩ := by
      rw [← mem_ofMask (t := ⟨t, ht⟩)]
      exact mem_ofMask_closN hT (imgN_lt hT u c) ⟨t, ht⟩
    have h2 : (Chk.imgN T (nroots m) u (Chk.closN T (dim m) (nroots m) c)).testBit t = true ↔
        Vanish m (cent m (ofMask m c)) (rtRoot hT u ⟨t, ht⟩) := by
      rw [testBit_imgN hT hinv (Chk.closN T (dim m) (nroots m) c) ⟨t, ht⟩,
        ← mem_ofMask (t := rtRoot hT u ⟨t, ht⟩)]
      exact mem_ofMask_closN hT hc (rtRoot hT u ⟨t, ht⟩)
    rw [h1, h2]
    exact vanish_cent_imgN hT hinv c ⟨t, ht⟩
  · have hle : 2 ^ nroots m ≤ 2 ^ t :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt ht)
    rw [Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le (closN_lt (T := T) (Chk.imgN T (nroots m) u c)) hle),
      Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le (imgN_lt hT u (Chk.closN T (dim m) (nroots m) c)) hle)]

private theorem growN_imgN (hT : Chk.tabsOK m T = true) {u : Root m}
    (hinv : ∀ t : Root m, (T.rt[u.val]!)[(T.rt[u.val]!)[t.val]!]! = t.val)
    (hadj : ∀ i j : Root m,
      (T.adj[(T.rt[u.val]!)[i.val]!]!).testBit ((T.rt[u.val]!)[j.val]!) =
        (T.adj[i.val]!).testBit j.val)
    (c' S : ℕ) :
    Chk.growN T (nroots m) (Chk.imgN T (nroots m) u c')
        (Chk.imgN T (nroots m) u S) =
      Chk.imgN T (nroots m) u (Chk.growN T (nroots m) c' S) := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < nroots m
  · apply Bool.eq_iff_iff.mpr
    rw [testBit_growN (c := Chk.imgN T (nroots m) u c')
      (S := Chk.imgN T (nroots m) u S) (t := t)]
    rw [testBit_imgN hT hinv (Chk.growN T (nroots m) c' S) ⟨t, ht⟩]
    rw [testBit_growN (c := c') (S := S) (t := (rtRoot hT u ⟨t, ht⟩).val)]
    rw [testBit_imgN hT hinv S ⟨t, ht⟩, testBit_imgN hT hinv c' ⟨t, ht⟩]
    constructor
    · rintro (h | ⟨s, hSs, hadjst, hc'⟩)
      · exact Or.inl h
      · refine Or.inr ⟨rtRoot hT u s, ?_, ?_, hc'⟩
        · exact (testBit_imgN hT hinv S s) ▸ hSs
        · exact (hadj s ⟨t, ht⟩).trans hadjst
    · rintro (h | ⟨s, hSs, hadjst, hc'⟩)
      · exact Or.inl h
      · refine Or.inr ⟨rtRoot hT u s, ?_, ?_, hc'⟩
        · rw [testBit_imgN hT hinv S (rtRoot hT u s), rtRoot_involutive hT hinv s]
          exact hSs
        · have h2 := hadj s (rtRoot hT u ⟨t, ht⟩)
          have h2' : (T.adj[(T.rt[u.val]!)[s.val]!]!).testBit t =
              (T.adj[s.val]!).testBit (rtRoot hT u ⟨t, ht⟩).val := by
            rw [show (T.rt[u.val]!)[(rtRoot hT u ⟨t, ht⟩).val]! = t from hinv ⟨t, ht⟩] at h2
            exact h2
          exact h2'.trans hadjst
  · have hpow : 2 ^ nroots m ≤ 2 ^ t :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt ht)
    rw [Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le (growN_lt_nroots hT (imgN_lt hT u S)) hpow),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (imgN_lt hT u _) hpow)]

private theorem repeat_imgN (hT : Chk.tabsOK m T = true) {u : Root m}
    (hinv : ∀ t : Root m, (T.rt[u.val]!)[(T.rt[u.val]!)[t.val]!]! = t.val)
    (hadj : ∀ i j : Root m,
      (T.adj[(T.rt[u.val]!)[i.val]!]!).testBit ((T.rt[u.val]!)[j.val]!) =
        (T.adj[i.val]!).testBit j.val)
    (c' S : ℕ) :
    ∀ n, Nat.repeat (Chk.growN T (nroots m) (Chk.imgN T (nroots m) u c')) n
        (Chk.imgN T (nroots m) u S) =
      Chk.imgN T (nroots m) u (Nat.repeat (Chk.growN T (nroots m) c') n S) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change Chk.growN T (nroots m) (Chk.imgN T (nroots m) u c')
        (Nat.repeat (Chk.growN T (nroots m) (Chk.imgN T (nroots m) u c')) n
          (Chk.imgN T (nroots m) u S)) =
      Chk.imgN T (nroots m) u (Chk.growN T (nroots m) c'
        (Nat.repeat (Chk.growN T (nroots m) c') n S))
    rw [ih]
    exact growN_imgN hT hinv hadj c' _

theorem growC_imgN (hT : Chk.tabsOK m T = true) {u : Root m}
    (hinv : ∀ t : Root m, (T.rt[u.val]!)[(T.rt[u.val]!)[t.val]!]! = t.val)
    (hadj : ∀ i j : Root m,
      (T.adj[(T.rt[u.val]!)[i.val]!]!).testBit ((T.rt[u.val]!)[j.val]!) =
        (T.adj[i.val]!).testBit j.val)
    {c : ℕ} (hc : c < 2 ^ nroots m) :
    Chk.growC T (dim m) (nroots m) (Chk.imgN T (nroots m) u c) =
      Chk.imgN T (nroots m) u (Chk.growC T (dim m) (nroots m) c) := by
  unfold Chk.growC
  rw [closN_imgN hT hinv hc]
  exact repeat_imgN hT hinv hadj (Chk.closN T (dim m) (nroots m) c) c (nroots m)

end CFSG.StandardType.GGQ2Frame.ExcRaw

end
