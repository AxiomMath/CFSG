module

public import CFSG.Quasithin.H13.AS91Sec3Base
public import Certificates.Data.CFSGNative.AS91.M24Geom

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Monster.Code

theorem maskFin_inj {a b : ℕ} (ha : a < 2 ^ 24) (hb : b < 2 ^ 24) (h : maskFin a = maskFin b) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 24
  · have h1 : (⟨i, hi⟩ : Fin 24) ∈ maskFin a ↔ (⟨i, hi⟩ : Fin 24) ∈ maskFin b := by rw [h]
    simp only [mem_maskFin] at h1
    cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · have hle : 2 ^ 24 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha hle),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb hle)]

theorem foldl_pop (m : ℕ) : ∀ (n a : ℕ),
    (List.range n).foldl (fun acc i => if m.testBit i = true then acc + 1 else acc) a =
      a + ∑ i ∈ Finset.range n, if m.testBit i = true then 1 else 0
  | 0, a => by simp
  | n + 1, a => by
    rw [List.range_succ, List.foldl_append, foldl_pop m n a, Finset.sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    split_ifs <;> omega

theorem card_maskFin (m : ℕ) : (maskFin m).card = Native.pop m := by
  unfold Native.pop
  rw [foldl_pop, zero_add, maskFin, Finset.card_filter,
    ← Fin.sum_univ_eq_sum_range (fun i => if m.testBit i = true then 1 else 0)]

theorem maskFin_and (a b : ℕ) : maskFin (a &&& b) = maskFin a ∩ maskFin b := by
  ext i
  simp only [mem_maskFin, Nat.testBit_and, Bool.and_eq_true, Finset.mem_inter]

theorem maskFin_or (a b : ℕ) : maskFin (a ||| b) = maskFin a ∪ maskFin b := by
  ext i
  simp only [mem_maskFin, Nat.testBit_or, Bool.or_eq_true, Finset.mem_union]

theorem maskFin_xor (a b : ℕ) : maskFin (a ^^^ b) = symmDiff (maskFin a) (maskFin b) := by
  ext i
  simp only [mem_maskFin, Nat.testBit_xor, Finset.mem_symmDiff]
  cases a.testBit i <;> cases b.testBit i <;> simp

theorem disjoint_maskFin (a b : ℕ) :
    Disjoint (maskFin a) (maskFin b) ↔ maskFin (a &&& b) = ∅ := by
  rw [maskFin_and, Finset.disjoint_iff_inter_eq_empty]

theorem maskFin_full : maskFin Native.full = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro i
  rw [mem_maskFin]
  revert i
  decide +kernel

theorem maskFin_eq_empty {m : ℕ} (h : m < 2 ^ 24) : maskFin m = ∅ ↔ m = 0 := by
  constructor
  · intro he
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit]
    by_cases hi : i < 24
    · by_contra hne
      have hmem : (⟨i, hi⟩ : Fin 24) ∈ maskFin m := mem_maskFin.2 (by simpa using hne)
      rw [he] at hmem
      simp at hmem
    · exact Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega)))
  · rintro rfl
    ext i
    simp [mem_maskFin]

theorem testBit_foldl_img (m : ℕ) (f : ℕ → ℕ) (j : ℕ) : ∀ (l : List ℕ) (a : ℕ),
    (l.foldl (fun acc i => if m.testBit i = true then acc ||| (1 <<< f i) else acc) a).testBit j =
        true ↔
      a.testBit j = true ∨ ∃ i ∈ l, m.testBit i = true ∧ f i = j := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons x l ih =>
    intro a
    rw [List.foldl_cons, ih]
    by_cases hx : m.testBit x = true
    · simp only [hx, ↓reduceIte, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow,
        Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨i, hi, h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨x, Or.inl rfl, hx, h⟩
        · exact Or.inr ⟨i, Or.inr hi, h1, h2⟩
      · rintro (h | ⟨i, (rfl | hi), h1, h2⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h2)
        · exact Or.inr ⟨i, hi, h1, h2⟩
    · simp only [hx, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      constructor
      · rintro (h | ⟨i, hi, h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨i, Or.inr hi, h1, h2⟩
      · rintro (h | ⟨i, (rfl | hi), h1, h2⟩)
        · exact Or.inl h
        · exact absurd h1 hx
        · exact Or.inr ⟨i, hi, h1, h2⟩

theorem testBit_img (t : Array ℕ) (m j : ℕ) :
    (Native.img t m).testBit j = true ↔ ∃ i < 24, m.testBit i = true ∧ t[i]! = j := by
  rw [Native.img, testBit_foldl_img]
  simp [List.mem_range]

theorem maskFin_img {t : Array ℕ} {g : Equiv.Perm (Fin 24)} (h : RepT t g) (m : ℕ) :
    maskFin (Native.img t m) = g • maskFin m := by
  ext j
  rw [mem_maskFin, testBit_img, Finset.mem_smul_finset]
  constructor
  · rintro ⟨i, hi, hm, hj⟩
    refine ⟨⟨i, hi⟩, mem_maskFin.2 hm, Fin.ext ?_⟩
    rw [Equiv.Perm.smul_def, ← h ⟨i, hi⟩]
    exact hj
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, i.2, mem_maskFin.1 hi, h i⟩

theorem img_lt {t : Array ℕ} {g : Equiv.Perm (Fin 24)} (h : RepT t g) (m : ℕ) :
    Native.img t m < 2 ^ 24 := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  by_contra hne
  rw [Bool.not_eq_false, testBit_img] at hne
  obtain ⟨i, hi, -, hij⟩ := hne
  have h1 := h ⟨i, hi⟩
  have hlt := (g ⟨i, hi⟩).2
  simp only at h1
  omega

theorem actM_eq_actM (cs : List ℕ) :
    ∀ m : ℕ, Native.actM cs m = CFSG.Quasithin.H.Mathieu.actM cs m := by
  induction cs with
  | nil => intro m; rfl
  | cons c cs ih =>
    intro m
    simp only [Native.actM, CFSG.Quasithin.H.Mathieu.actM, ih]

theorem synd_eq_syndM (m : ℕ) : Native.synd m = CFSG.Quasithin.H.Mathieu.syndM m := by
  unfold Native.synd CFSG.Quasithin.H.Mathieu.syndM
  rw [actM_eq_actM]
  rfl

theorem eY_maskFin (m : ℕ) : eY (maskFin m) = Multiplicative.ofAdd (bvec 24 m) := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [toAdd_eY, toAdd_ofAdd, bvec_apply]
  by_cases h : m.testBit i = true <;> simp [h, mem_maskFin]

theorem eY_maskFin_mem_golayC {m : ℕ} (_h : m < 2 ^ 24) :
    eY (maskFin m) ∈ golayC ↔ Native.synd m = 0 := by
  rw [eY_maskFin, mem_golayC_iff', toAdd_ofAdd, CFSG.Quasithin.H.Mathieu.bvec_mem_C_iff,
    synd_eq_syndM]

end CFSG.Quasithin.H13.AS91.M24G
