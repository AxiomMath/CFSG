module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRaw

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

open Module

namespace RootFacts

@[expose] noncomputable def band (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def bor (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def allN (n : ℕ) (p : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => band (p i) ih) n

@[expose] noncomputable def anyN (n : ℕ) (p : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => bor (p i) ih) n

@[expose] noncomputable def sumN (n : ℕ) (f : ℕ → ℤ) : ℤ :=
  Nat.rec (motive := fun _ => ℤ) 0 (fun k s => s + f k) n

@[expose] noncomputable def fI (m : Fin 6) (i k : ℕ) : ℤ := ((tabF m).getD i []).getD k 0

@[expose] noncomputable def hI (m : Fin 6) (i k : ℕ) : ℤ := ((tabH m).getD i []).getD k 0

@[expose] noncomputable def pairI (m : Fin 6) (i j : ℕ) : ℤ :=
  if m.val = 3 then sumN 6 fun k => fI 2 i k * hI 2 j k
  else sumN (dim m) fun k => fI m i k * hI m j k

@[expose] noncomputable def dotL : List ℤ → List ℤ → ℤ :=
  List.rec (motive := fun _ => List ℤ → ℤ) (fun _ => 0)
    (fun a _ ih ys => List.rec (motive := fun _ => ℤ) 0 (fun b ys' _ => a * b + ih ys') ys)

@[expose] noncomputable def bndB (p : ℤ) : Bool := band (decide (-2 ≤ p)) (decide (p ≤ 2))

@[expose] noncomputable def boundRow (f : List ℤ) (Hs : List (List ℤ)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun h _ ih => band (bndB (dotL f h)) ih) Hs

@[expose] noncomputable def boundL (Fs Hs : List (List ℤ)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun f _ ih => band (boundRow f Hs) ih) Fs

@[expose] noncomputable def lenOK (Fs : List (List ℤ)) (d : ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun f _ ih => band (decide (f.length ≤ d)) ih) Fs

@[expose] noncomputable def distinctB (m : Fin 6) : Bool :=
  allN (nroots m) fun a => (fun fa : List ℤ => allN a fun b => (fun fb : List ℤ =>
    band (anyN (dim m) fun k => !((fa.getD k 0 - fb.getD k 0) % 3 == 0))
      (anyN (dim m) fun k => !((fa.getD k 0 + fb.getD k 0) % 3 == 0)))
      ((tabF m).getD b [])) ((tabF m).getD a [])

@[expose] noncomputable def rowEq (t' u t : ℕ) (ε : ℤ) : Bool :=
  (fun (r rt ru : List ℤ) (p : ℤ) =>
    allN 4 fun k => (r.getD k 0 - ε * (rt.getD k 0 - p * ru.getD k 0)) % 3 == 0)
    ((tabF 1).getD t' []) ((tabF 1).getD t []) ((tabF 1).getD u []) (pairI 1 t u)

@[expose] noncomputable def fixB : Bool :=
  allN 24 fun u => allN 24 fun t => allN 24 fun t' =>
    bor (tabFix1.getD t' false == tabFix1.getD t false)
      (!(bor (rowEq t' u t 1) (rowEq t' u t (-1))))

theorem band_eq_true {a b : Bool} : band a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem bor_eq_true {a b : Bool} : bor a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem allN_iff {n : ℕ} {p : ℕ → Bool} : allN n p = true ↔ ∀ i < n, p i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change band (p n) (allN n p) = true ↔ _
    rw [band_eq_true, ih]
    constructor
    · rintro ⟨hn, h⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h i hi
      · exact hn
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem anyN_iff {n : ℕ} {p : ℕ → Bool} : anyN n p = true ↔ ∃ i < n, p i = true := by
  induction n with
  | zero => exact ⟨fun h => (Bool.false_ne_true h).elim, fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    change bor (p n) (anyN n p) = true ↔ _
    rw [bor_eq_true, ih]
    constructor
    · rintro (hn | ⟨i, hi, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, hn⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

theorem sumN_eq (n : ℕ) (f : ℕ → ℤ) : sumN n f = ∑ k : Fin n, f k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change sumN n f + f n = _
    rw [ih, Fin.sum_univ_castSucc]
    rfl

theorem pairI_eq (m : Fin 6) (i j : Root m) : pairI m i j = pairing m i j := by
  rw [pairI, pairing]
  split_ifs
  · rw [sumN_eq]
    rfl
  · rw [sumN_eq]
    rfl

theorem dotL_eq (f h : List ℤ) (d : ℕ) (hf : f.length ≤ d) :
    dotL f h = ∑ k : Fin d, f.getD k 0 * h.getD k 0 := by
  induction f generalizing h d with
  | nil =>
    change (0 : ℤ) = _
    simp
  | cons a f ih =>
    cases h with
    | nil =>
      change (0 : ℤ) = _
      simp
    | cons b h =>
      obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by simp at hf; omega⟩
      change a * b + dotL f h = _
      rw [Fin.sum_univ_succ, ih h d (by simp at hf; omega)]
      simp

theorem boundRow_spec {f : List ℤ} {Hs : List (List ℤ)} (hb : boundRow f Hs = true) :
    ∀ h ∈ Hs, bndB (dotL f h) = true := by
  induction Hs with
  | nil => simp
  | cons h Hs ih =>
    change band (bndB (dotL f h)) (boundRow f Hs) = true at hb
    rw [band_eq_true] at hb
    intro h' hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hb.1
    · exact ih hb.2 h' hm

theorem boundL_spec {Fs Hs : List (List ℤ)} (hb : boundL Fs Hs = true) :
    ∀ f ∈ Fs, ∀ h ∈ Hs, bndB (dotL f h) = true := by
  induction Fs with
  | nil => simp
  | cons f Fs ih =>
    change band (boundRow f Hs) (boundL Fs Hs) = true at hb
    rw [band_eq_true] at hb
    intro f' hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact boundRow_spec hb.1
    · exact ih hb.2 f' hm

theorem lenOK_spec {Fs : List (List ℤ)} {d : ℕ} (hb : lenOK Fs d = true) :
    ∀ f ∈ Fs, f.length ≤ d := by
  induction Fs with
  | nil => simp
  | cons f Fs ih =>
    change band (decide (f.length ≤ d)) (lenOK Fs d) = true at hb
    rw [band_eq_true, decide_eq_true_eq] at hb
    intro f' hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hb.1
    · exact ih hb.2 f' hm

theorem getD_mem_or (L : List (List ℤ)) (i : ℕ) : L.getD i [] ∈ L ∨ L.getD i [] = [] := by
  rw [List.getD_eq_getElem?_getD]
  cases h : L[i]? with
  | none => exact Or.inr rfl
  | some x => exact Or.inl (List.mem_of_getElem? h)

theorem bound_of {Fs Hs : List (List ℤ)} {d : ℕ} (hb : boundL Fs Hs = true)
    (hl : lenOK Fs d = true) (i j : ℕ) :
    -2 ≤ ∑ k : Fin d, (Fs.getD i []).getD k 0 * (Hs.getD j []).getD k 0 ∧
      ∑ k : Fin d, (Fs.getD i []).getD k 0 * (Hs.getD j []).getD k 0 ≤ 2 := by
  rcases getD_mem_or Fs i with hf | hf
  · rcases getD_mem_or Hs j with hh | hh
    · have h := boundL_spec hb _ hf _ hh
      rw [bndB, band_eq_true, decide_eq_true_eq, decide_eq_true_eq,
        dotL_eq _ _ d (lenOK_spec hl _ hf)] at h
      exact h
    · rw [hh]
      simp
  · rw [hf]
    simp

theorem boundL_eq (m : Fin 6) (hm : m.val ≠ 3) : boundL (tabF m) (tabH m) = true := by
  fin_cases m
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact absurd rfl hm
  · decide +kernel
  · decide +kernel

theorem lenOK_eq (m : Fin 6) : lenOK (tabF m) (dim m) = true := by
  fin_cases m <;> decide +kernel

theorem distinctB_eq (m : Fin 6) : distinctB m = true := by
  fin_cases m <;> decide +kernel

theorem fixB_eq : fixB = true := by
  decide +kernel

theorem int_emod_three_eq_zero_iff (z : ℤ) : z % 3 = 0 ↔ (z : ZMod 3) = 0 := by
  rw [← Int.dvd_iff_emod_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num

end RootFacts

open RootFacts

theorem pairing_bound (m : Fin 6) (i j : Root m) : -2 ≤ pairing m i j ∧ pairing m i j ≤ 2 := by
  rw [pairing]
  split_ifs with hm
  · exact bound_of (boundL_eq 2 (by decide)) (lenOK_eq 2) i j
  · exact bound_of (boundL_eq m hm) (lenOK_eq m) i j

theorem pairing_eq_zero_iff (m : Fin 6) (i j : Root m) :
    pairing m i j = 0 ↔ (pairing m i j : ZMod 3) = 0 := by
  rw [← int_emod_three_eq_zero_iff]
  have h := pairing_bound m i j
  omega

theorem root_single (m : Fin 6) (i : Root m) (k : Fin (dim m)) :
    root m i (Pi.single k 1) = (F m i k : ZMod 3) := by
  rw [root_apply, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem root_reflection_apply (m : Fin 6) (t u : Root m) (v : V m) :
    root m t (reflection m u v) = root m t v - (pairing m t u : ZMod 3) * root m u v := by
  rw [reflection_apply, map_sub, map_smul, pairing_eq, smul_eq_mul,
    mul_comm ((root m u) v) ((pairing m t u : ZMod 3))]
  rfl

private theorem distinct_lt {m : Fin 6} {a b : Root m} (hab : b.val < a.val) :
    (∃ k : Fin (dim m), ((F m a k - F m b k : ℤ) : ZMod 3) ≠ 0) ∧
      ∃ k : Fin (dim m), ((F m a k + F m b k : ℤ) : ZMod 3) ≠ 0 := by
  have h := allN_iff.mp (allN_iff.mp (distinctB_eq m) a.val a.isLt) b.val hab
  beta_reduce at h
  rw [band_eq_true, anyN_iff, anyN_iff] at h
  obtain ⟨⟨k, hk, h1⟩, ⟨k', hk', h2⟩⟩ := h
  refine ⟨⟨⟨k, hk⟩, fun h0 => ?_⟩, ⟨⟨k', hk'⟩, fun h0 => ?_⟩⟩
  · rw [← int_emod_three_eq_zero_iff] at h0
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne] at h1
    exact h1 h0
  · rw [← int_emod_three_eq_zero_iff] at h0
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne] at h2
    exact h2 h0

private theorem distinct_ne {m : Fin 6} {a b : Root m} (hab : a ≠ b) :
    (∃ k : Fin (dim m), ((F m a k - F m b k : ℤ) : ZMod 3) ≠ 0) ∧
      ∃ k : Fin (dim m), ((F m a k + F m b k : ℤ) : ZMod 3) ≠ 0 := by
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
  · obtain ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩ := distinct_lt (a := b) (b := a) h
    refine ⟨⟨k, fun he => hk ?_⟩, ⟨k', ?_⟩⟩
    · rw [← neg_sub, Int.cast_neg, he]
      exact neg_zero
    · rwa [add_comm]
  · exact distinct_lt h

theorem eq_of_root_eq_sign {m : Fin 6} {a b : Root m} {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (h : ∀ v, root m a v = (ε : ZMod 3) * root m b v) : a = b := by
  by_contra hab
  obtain ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩ := distinct_ne hab
  rcases hε with rfl | rfl
  · apply hk
    have := h (Pi.single k 1)
    rw [root_single, root_single, Int.cast_one, one_mul] at this
    rw [Int.cast_sub, this, sub_self]
  · apply hk'
    have := h (Pi.single k' 1)
    rw [root_single, root_single, Int.cast_neg, Int.cast_one, neg_one_mul] at this
    rw [Int.cast_add, this, neg_add_cancel]

theorem tabFix1_eq_of_root {u t t' : Root 1} {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (h : ∀ v, root 1 t' v = (ε : ZMod 3) * root 1 t (reflection 1 u v)) :
    tabFix1.getD t'.val false = tabFix1.getD t.val false := by
  have hrow : rowEq t'.val u.val t.val ε = true := by
    unfold rowEq
    beta_reduce
    refine allN_iff.mpr fun k hk => ?_
    have hv := h (Pi.single ⟨k, hk⟩ 1)
    rw [root_reflection_apply, root_single, root_single, root_single] at hv
    rw [beq_iff_eq, int_emod_three_eq_zero_iff, pairI_eq 1 t u]
    push_cast
    change (F 1 t' ⟨k, hk⟩ : ZMod 3) - (ε : ZMod 3) * ((F 1 t ⟨k, hk⟩ : ZMod 3) -
      (pairing 1 t u : ZMod 3) * (F 1 u ⟨k, hk⟩ : ZMod 3)) = 0
    rw [hv, sub_self]
  have hfix := allN_iff.mp (allN_iff.mp (allN_iff.mp fixB_eq u.val u.isLt) t.val t.isLt)
    t'.val t'.isLt
  rw [bor_eq_true] at hfix
  rcases hfix with he | hn
  · exact beq_iff_eq.mp he
  · exfalso
    rw [Bool.not_eq_true', ← Bool.not_eq_true, bor_eq_true] at hn
    apply hn
    rcases hε with rfl | rfl
    · exact Or.inl hrow
    · exact Or.inr hrow

end CFSG.StandardType.GGQ2Frame.ExcRaw
