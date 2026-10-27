module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusChecks
public import Certificates.Data.CFSGNative.ExcCensus.Inside

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

variable {m : Fin 6} {T : Chk.Tabs}

theorem root_rt_eq (hT : Chk.tabsOK m T = true) (u t : Root m) :
    ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v : V m,
      root m ⟨(T.rt[u.val]!)[t.val]!, tabsOK_rt_lt hT u t⟩ v = ε * root m t (reflection m u v) := by
  have hrt := nat_all_iff.mp (nat_all_iff.mp (tabsOK_rtN hT) u.val u.isLt) t.val t.isLt
  have h := (Bool.or_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hrt).2
  rcases h with h1 | h1
  · refine ⟨(1 : ZMod 3), Or.inl (by norm_num), fun v => ?_⟩
    rw [root_rt hT u t ⟨_, tabsOK_rt_lt hT u t⟩ 1 h1 v, root_reflection m t u v]
    push_cast
    ring_nf
  · refine ⟨(-1 : ZMod 3), Or.inr (by norm_num), fun v => ?_⟩
    have h := root_rt hT u t ⟨_, tabsOK_rt_lt hT u t⟩ (-1) h1 v
    rw [root_reflection m t u v]
    push_cast at h ⊢
    exact h

private theorem testBit_false_of_lt_two_pow {n x i : ℕ} (hx : x < 2 ^ n) (hi : n ≤ i) :
    x.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi))

private theorem imgN_fold_lt (hT : Chk.tabsOK m T = true) (u : Root m) (c : ℕ) :
    ∀ n, n ≤ nroots m →
      Nat.fold n (fun t _ acc => if c.testBit t then acc ||| 1 <<< (T.rt[u.val]!)[t]! else acc) 0
        < 2 ^ nroots m := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [Nat.fold_succ]
    split_ifs with hc
    · refine Nat.or_lt_two_pow (ih (by omega)) ?_
      rw [Nat.one_shiftLeft]
      exact Nat.pow_lt_pow_right (by norm_num) (tabsOK_rt_lt hT u ⟨n, by omega⟩)
    · exact ih (by omega)

theorem imgN_lt (hT : Chk.tabsOK m T = true) (u : Root m) (c : ℕ) :
    Chk.imgN T (nroots m) u c < 2 ^ nroots m := by
  unfold Chk.imgN
  exact imgN_fold_lt hT u c (nroots m) le_rfl

private theorem imgN_fold_testBit (u : Root m) (c : ℕ) :
    ∀ (n x : ℕ),
      (Nat.fold n (fun t _ acc => if c.testBit t then acc ||| 1 <<< (T.rt[u.val]!)[t]! else acc)
        0).testBit x = true ↔
        ∃ s, s < n ∧ c.testBit s = true ∧ (T.rt[u.val]!)[s]! = x := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    rw [Nat.fold_succ]
    by_cases hc : c.testBit n = true
    · rw [if_pos hc, Nat.testBit_lor, Bool.or_eq_true, ih, Nat.one_shiftLeft,
        Nat.testBit_two_pow, decide_eq_true_eq]
      constructor
      · rintro (⟨s, hs, hcs, hrt⟩ | hrt)
        · exact ⟨s, by omega, hcs, hrt⟩
        · exact ⟨n, Nat.lt_succ_self n, hc, hrt⟩
      · rintro ⟨s, hs, hcs, hrt⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs' | rfl
        · exact Or.inl ⟨s, hs', hcs, hrt⟩
        · exact Or.inr hrt
    · rw [if_neg hc, ih]
      constructor
      · rintro ⟨s, hs, hcs, hrt⟩
        exact ⟨s, by omega, hcs, hrt⟩
      · rintro ⟨s, hs, hcs, hrt⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs' | rfl
        · exact ⟨s, hs', hcs, hrt⟩
        · exact absurd hcs hc

theorem mem_ofMask_imgN (u : Root m) (c : ℕ) (t : Root m) :
    t ∈ ofMask m (Chk.imgN T (nroots m) u c) ↔
      ∃ s : Root m, s ∈ ofMask m c ∧ (T.rt[u.val]!)[s.val]! = t.val := by
  rw [mem_ofMask, Chk.imgN, imgN_fold_testBit u c (nroots m) t.val]
  constructor
  · rintro ⟨s, hs, hcs, hrt⟩
    exact ⟨⟨s, hs⟩, mem_ofMask.mpr hcs, hrt⟩
  · rintro ⟨s, hcs, hrt⟩
    exact ⟨s.val, s.isLt, mem_ofMask.mp hcs, hrt⟩

private theorem closN_fold_lt (c : ℕ) :
    ∀ n, Nat.fold n (fun v _ acc => if Chk.subN c (T.zm[v]!) then acc &&& (T.zm[v]!) else acc)
      (2 ^ nroots m - 1) < 2 ^ nroots m := by
  intro n
  induction n with
  | zero =>
    simp only [Nat.fold_zero]
    exact Nat.sub_one_lt (Nat.two_pow_pos _).ne'
  | succ n ih =>
    rw [Nat.fold_succ]
    split_ifs with h
    · exact lt_of_le_of_lt Nat.and_le_left ih
    · exact ih

theorem closN_lt (c : ℕ) : Chk.closN T (dim m) (nroots m) c < 2 ^ nroots m := by
  unfold Chk.closN
  exact closN_fold_lt c (3 ^ dim m)

private theorem subN_iff_testBit {c z : ℕ} (hc : c < 2 ^ nroots m) :
    Chk.subN c z = true ↔ ∀ i, i < nroots m → c.testBit i = true → z.testBit i = true := by
  rw [Chk.subN, beq_iff_eq]
  constructor
  · intro h i hi hci
    have h1 : (c &&& z).testBit i = true := by rw [h]; exact hci
    simpa [Nat.testBit_and, hci] using h1
  · intro h
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [Nat.testBit_and]
    by_cases hi : i < nroots m
    · by_cases hci : c.testBit i = true
      · rw [h i hi hci, hci]
        rfl
      · have hcif : c.testBit i = false := by
          cases hb : c.testBit i with
          | false => rfl
          | true => exact absurd hb hci
        rw [hcif]
        rfl
    · rw [testBit_false_of_lt_two_pow hc (Nat.le_of_not_lt hi)]
      rfl

private theorem closN_fold_testBit {c : ℕ} (t : ℕ) :
    ∀ n, n ≤ 3 ^ dim m →
      ((Nat.fold n (fun v _ acc => if Chk.subN c (T.zm[v]!) then acc &&& (T.zm[v]!) else acc)
        (2 ^ nroots m - 1)).testBit t = true ↔
        t < nroots m ∧ ∀ v, v < n → Chk.subN c (T.zm[v]!) = true →
          (T.zm[v]!).testBit t = true) := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [Nat.fold_zero, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
    constructor
    · intro ht
      exact ⟨ht, by omega⟩
    · rintro ⟨ht, _⟩
      exact ht
  | succ n ih =>
    intro hn
    rw [Nat.fold_succ]
    by_cases hcond : Chk.subN c (T.zm[n]!) = true
    · rw [if_pos hcond, Nat.testBit_and, Bool.and_eq_true, ih (by omega)]
      constructor
      · rintro ⟨⟨ht, hall⟩, hbit⟩
        refine ⟨ht, ?_⟩
        intro v hv hsub
        rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv' | rfl
        · exact hall v hv' hsub
        · exact hbit
      · rintro ⟨ht, hall⟩
        refine ⟨⟨ht, ?_⟩, ?_⟩
        · intro v hv hsub
          exact hall v (by omega) hsub
        · exact hall n (Nat.lt_succ_self n) hcond
    · rw [if_neg hcond, ih (by omega)]
      constructor
      · rintro ⟨ht, hall⟩
        refine ⟨ht, ?_⟩
        intro v hv hsub
        rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv' | rfl
        · exact hall v hv' hsub
        · exact absurd hsub hcond
      · rintro ⟨ht, hall⟩
        exact ⟨ht, fun v hv hsub => hall v (by omega) hsub⟩

theorem mem_ofMask_closN (hT : Chk.tabsOK m T = true) {c : ℕ} (hc : c < 2 ^ nroots m)
    (t : Root m) :
    t ∈ ofMask m (Chk.closN T (dim m) (nroots m) c) ↔ Vanish m (cent m (ofMask m c)) t := by
  rw [mem_ofMask, Chk.closN, closN_fold_testBit t.val (3 ^ dim m) le_rfl]
  constructor
  · rintro ⟨ht, hall⟩ w hw
    have hw' : ∀ i ∈ ofMask m c, root m i w = 0 := by
      simpa only [cent, Submodule.mem_iInf, LinearMap.mem_ker] using hw
    have hv : code m w < 3 ^ dim m := code_lt m w
    have hsub : Chk.subN c (T.zm[code m w]!) = true := by
      rw [subN_iff_testBit hc]
      intro i hi hci
      exact mem_ofMask.mp ((mem_ofMask_zm hT hv ⟨i, hi⟩).mpr (by
        rw [vec_code]
        exact hw' ⟨i, hi⟩ (mem_ofMask.mpr hci)))
    have hbit : (T.zm[code m w]!).testBit t.val = true := hall (code m w) hv hsub
    rw [← mem_ofMask] at hbit
    rwa [mem_ofMask_zm hT hv t, vec_code] at hbit
  · intro hvan
    refine ⟨t.isLt, ?_⟩
    intro v hv hsub
    have hmem : vec m v ∈ cent m (ofMask m c) := by
      simp only [cent, Submodule.mem_iInf, LinearMap.mem_ker]
      intro i hi
      have hzi : (T.zm[v]!).testBit i.val = true :=
        (subN_iff_testBit hc).mp hsub i.val i.isLt (mem_ofMask.mp hi)
      exact (mem_ofMask_zm hT hv i).mp (mem_ofMask.mpr hzi)
    exact mem_ofMask.mp ((mem_ofMask_zm hT hv t).mpr (hvan (vec m v) hmem))

private theorem growN_fold_mono {c' S : ℕ} :
    ∀ (n x : ℕ), S.testBit x = true →
      (Nat.fold n (fun t _ acc => if S.testBit t then acc ||| (T.adj[t]! &&& c') else acc)
        S).testBit x = true := by
  intro n
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
    intro x hx
    rw [Nat.fold_succ]
    by_cases hbit : S.testBit n = true
    · rw [if_pos hbit, Nat.testBit_lor, ih x hx]
      rfl
    · rw [if_neg hbit]
      exact ih x hx

private theorem growN_mono {c' S x : ℕ} (hS : S.testBit x = true) :
    (Chk.growN T (nroots m) c' S).testBit x = true := by
  unfold Chk.growN
  exact growN_fold_mono (nroots m) x hS

private theorem repeat_growN_mono {c' : ℕ} :
    ∀ (n S x : ℕ), S.testBit x = true →
      (Nat.repeat (Chk.growN T (nroots m) c') n S).testBit x = true := by
  intro n
  induction n with
  | zero => intro S x h; simpa [Nat.repeat] using h
  | succ n ih =>
    intro S x h
    rw [show Nat.repeat (Chk.growN T (nroots m) c') (n + 1) S
        = Chk.growN T (nroots m) c' (Nat.repeat (Chk.growN T (nroots m) c') n S) from rfl]
    exact growN_mono (ih S x h)

theorem subset_growC (c : ℕ) : ofMask m c ⊆ ofMask m (Chk.growC T (dim m) (nroots m) c) := by
  intro t ht
  rw [mem_ofMask] at ht ⊢
  unfold Chk.growC
  exact repeat_growN_mono (nroots m) c t.val ht

theorem growC_subset (hT : Chk.tabsOK m T = true) {c : ℕ} (hc : c < 2 ^ nroots m)
    {C : Finset (Root m)} (hcC : ofMask m c ⊆ C)
    (hC : ∀ i ∈ C, ∀ j, Vanish m (cent m (ofMask m c)) j → Adj m i j → j ∈ C) :
    ofMask m (Chk.growC T (dim m) (nroots m) c) ⊆ C := by
  intro t ht
  rw [mem_ofMask] at ht
  unfold Chk.growC at ht
  have hspec := growN_repeat_spec hT C
    (c := Chk.closN T (dim m) (nroots m) c)
    (c' := Chk.closN T (dim m) (nroots m) c)
    (start := c)
    (fun _ _ hbit => mem_ofMask.mpr hbit)
    (fun i hi j hj hadj => hC i hi j ((mem_ofMask_closN hT hc j).mp hj) hadj)
    (fun _ _ hbit => hcC (mem_ofMask.mpr hbit))
    (fun _ ht => testBit_false_of_lt_two_pow hc ht)
    (fun _ ht => testBit_false_of_lt_two_pow (closN_lt c) ht)
    (nroots m)
  exact hspec.2 t.val t.isLt ht

end CFSG.StandardType.GGQ2Frame.ExcRaw
