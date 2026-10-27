module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bMeasure
import Mathlib.Combinatorics.Colex

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley

@[expose] def levTwoS3bK_e8_condES (m : ℕ) (l : List ℤ) (e : ℕ) (sg : ℤ) : Bool :=
  (e == 0 || m.testBit 0) &&
    (List.range 8).all (fun j =>
      decide (0 ≤ sg * l.getD j 0 + (e : ℤ) * levTwoS3b_theta.getD j 0) &&
        (sg * l.getD j 0 + (e : ℤ) * levTwoS3b_theta.getD j 0 == 0 || m.testBit (j + 1)))

@[expose] def levTwoS3bK_e8_cond (m : ℕ) (l : List ℤ) : Bool :=
  levTwoS3bK_e8_condES m l 0 1 || levTwoS3bK_e8_condES m l 0 (-1) ||
    levTwoS3bK_e8_condES m l 1 1 || levTwoS3bK_e8_condES m l 1 (-1)

@[expose] def levTwoS3bK_e8_walk (m : ℕ) : List ℤ → ℕ → Bool :=
  List.rec (fun _ => true) (fun x _ ih p =>
    decide (0 ≤ x) && (x == 0 || Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 p))) && ih (p + 1))

@[expose] def levTwoS3bK_e8_condW (m : ℕ) (l : List ℤ) : Bool :=
  levTwoS3bK_e8_walk m l 1 || levTwoS3bK_e8_walk m (l.map (fun x => -x)) 1 ||
    (Nat.blt 0 (Nat.land m 1) &&
      (levTwoS3bK_e8_walk m (List.zipWith (fun x t => x + t) l levTwoS3b_theta) 1 ||
        levTwoS3bK_e8_walk m (List.zipWith (fun x t => t - x) l levTwoS3b_theta) 1))

@[expose] def levTwoS3bK_e8_chk (k : ℕ) : Bool :=
  (List.range 64).all (fun i => 64 * k + i == 511 ||
    levTwoS3b_roots.all (fun l =>
      levTwoS3bK_e8_condW (64 * k + i) l == levTwoS3b_inPat (64 * k + i) l))

theorem levTwoS3bK_e8_chk_0 : levTwoS3bK_e8_chk 0 = true := by decide +kernel
theorem levTwoS3bK_e8_chk_1 : levTwoS3bK_e8_chk 1 = true := by decide +kernel
theorem levTwoS3bK_e8_chk_2 : levTwoS3bK_e8_chk 2 = true := by decide +kernel
theorem levTwoS3bK_e8_chk_3 : levTwoS3bK_e8_chk 3 = true := by decide +kernel
theorem levTwoS3bK_e8_chk_4 : levTwoS3bK_e8_chk 4 = true := by decide +kernel
theorem levTwoS3bK_e8_chk_5 : levTwoS3bK_e8_chk 5 = true := by decide +kernel
theorem levTwoS3bK_e8_chk_6 : levTwoS3bK_e8_chk 6 = true := by decide +kernel
theorem levTwoS3bK_e8_chk_7 : levTwoS3bK_e8_chk 7 = true := by decide +kernel

theorem levTwoS3bK_testBit_sum {α : Type*} [DecidableEq α] (f : α → ℕ)
    (hf : Function.Injective f) (D : Finset α) (y : α) :
    (∑ x ∈ D, 2 ^ f x).testBit (f y) = decide (y ∈ D) := by
  have h1 : ∑ x ∈ D, 2 ^ f x = ∑ i ∈ D.map ⟨f, hf⟩, 2 ^ i := by
    rw [Finset.sum_map]
    rfl
  have h2 := Finset.toFinset_bitIndices_sum_two_pow (D.map ⟨f, hf⟩)
  rw [h1]
  apply Bool.eq_iff_iff.2
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, h2, Finset.mem_map]
  simp [hf.eq_iff]

theorem levTwoS3bK_e8_blt_land (m p : ℕ) :
    Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 p)) = m.testBit p := by
  have h : Nat.land m (Nat.shiftLeft 1 p) = m &&& 2 ^ p := by
    rw [← Nat.one_shiftLeft]
    rfl
  rw [h, Nat.and_two_pow]
  cases m.testBit p <;> simp <;> rfl

theorem levTwoS3bK_e8_walk_iff (m : ℕ) : ∀ (v : List ℤ) (p : ℕ),
    levTwoS3bK_e8_walk m v p = true ↔
      ∀ j (h : j < v.length), 0 ≤ v[j] ∧ (v[j] ≠ 0 → m.testBit (p + j) = true)
  | [], p => by simp [levTwoS3bK_e8_walk]
  | x :: v, p => by
    have ih := levTwoS3bK_e8_walk_iff m v (p + 1)
    change (decide (0 ≤ x) && (x == 0 || Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 p))) &&
      levTwoS3bK_e8_walk m v (p + 1)) = true ↔ _
    rw [levTwoS3bK_e8_blt_land, Bool.and_eq_true, Bool.and_eq_true, ih]
    simp only [decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, List.length_cons]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩ j hj
      cases j with
      | zero =>
        rw [List.getElem_cons_zero, Nat.add_zero]
        exact ⟨h1, fun hx => h2.resolve_left hx⟩
      | succ j =>
        have := h3 j (by omega)
        have e : p + (j + 1) = p + 1 + j := by omega
        rw [List.getElem_cons_succ, e]
        exact this
    · intro h
      refine ⟨⟨(h 0 (by omega)).1, ?_⟩, fun j hj => ?_⟩
      · by_cases hx : x = 0
        · exact Or.inl hx
        · exact Or.inr ((h 0 (by omega)).2 hx)
      · have := h (j + 1) (by omega)
        have e : p + 1 + j = p + (j + 1) := by omega
        rw [e]
        exact this

theorem levTwoS3bK_e8_walk_eq_all (m : ℕ) (V : List ℤ) (hV : V.length = 8) (F : ℕ → ℤ)
    (hF : ∀ j < 8, V.getD j 0 = F j) :
    levTwoS3bK_e8_walk m V 1 =
      (List.range 8).all (fun j => decide (0 ≤ F j) && (F j == 0 || m.testBit (j + 1))) := by
  apply Bool.eq_iff_iff.2
  rw [levTwoS3bK_e8_walk_iff]
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, beq_iff_eq]
  constructor
  · intro h j hj
    have hj' : j < V.length := by omega
    have hg := hF j hj
    rw [List.getD_eq_getElem _ _ hj'] at hg
    rw [← hg, Nat.add_comm j 1]
    refine ⟨(h j hj').1, ?_⟩
    by_cases hz : V[j] = 0
    · exact Or.inl hz
    · exact Or.inr ((h j hj').2 hz)
  · intro h j hj'
    have hj : j < 8 := by omega
    have hg := hF j hj
    rw [List.getD_eq_getElem _ _ hj'] at hg
    rw [hg, Nat.add_comm 1 j]
    exact ⟨(h j hj).1, fun hz => (h j hj).2.resolve_left hz⟩

theorem levTwoS3bK_e8_condW_eq (m : ℕ) (l : List ℤ) (hl : l.length = 8) :
    levTwoS3bK_e8_condW m l = levTwoS3bK_e8_cond m l := by
  have ht : levTwoS3b_theta.length = 8 := rfl
  have hlj : ∀ j < 8, j < l.length := fun j hj => by omega
  have htj : ∀ j < 8, j < levTwoS3b_theta.length := fun j hj => by omega
  have w0 := levTwoS3bK_e8_walk_eq_all m l hl
    (fun j => 1 * l.getD j 0 + ((0 : ℕ) : ℤ) * levTwoS3b_theta.getD j 0) (fun j _ => by simp)
  have w1 := levTwoS3bK_e8_walk_eq_all m (l.map (fun x => -x)) (by simp [hl])
    (fun j => -1 * l.getD j 0 + ((0 : ℕ) : ℤ) * levTwoS3b_theta.getD j 0) (fun j hj => by
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_map, hl]; omega), List.getElem_map,
        List.getD_eq_getElem _ _ (hlj j hj)]
      simp)
  have w2 := levTwoS3bK_e8_walk_eq_all m (List.zipWith (fun x t => x + t) l levTwoS3b_theta)
    (by simp [hl, ht])
    (fun j => 1 * l.getD j 0 + ((1 : ℕ) : ℤ) * levTwoS3b_theta.getD j 0) (fun j hj => by
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_zipWith, hl, ht]; omega),
        List.getElem_zipWith, List.getD_eq_getElem _ _ (hlj j hj),
        List.getD_eq_getElem _ _ (htj j hj)]
      simp)
  have w3 := levTwoS3bK_e8_walk_eq_all m (List.zipWith (fun x t => t - x) l levTwoS3b_theta)
    (by simp [hl, ht])
    (fun j => -1 * l.getD j 0 + ((1 : ℕ) : ℤ) * levTwoS3b_theta.getD j 0) (fun j hj => by
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_zipWith, hl, ht]; omega),
        List.getElem_zipWith, List.getD_eq_getElem _ _ (hlj j hj),
        List.getD_eq_getElem _ _ (htj j hj)]
      simp only [Nat.cast_one, one_mul, neg_one_mul]
      ring)
  have hb : Nat.blt 0 (Nat.land m 1) = m.testBit 0 := levTwoS3bK_e8_blt_land m 0
  rw [levTwoS3bK_e8_condW, w0, w1, w2, w3, hb, levTwoS3bK_e8_cond]
  simp only [levTwoS3bK_e8_condES]
  cases m.testBit 0 <;> simp [Bool.or_assoc]

variable (f : Option (Fin (Tag.rank Tag.E8)) → ℕ) (h0 : f none = 0)
  (hs : ∀ j, f (some j) = j.val + 1)

include h0 hs in
theorem levTwoS3bK_e8_idx_injective : Function.Injective f := by
  intro x y h
  cases x <;> cases y <;> simp_all [Fin.ext_iff]

include h0 hs in
theorem levTwoS3bK_e8_cond_iff (θ : Fin (Tag.rank Tag.E8) → ℤ)
    (hθ : ∀ j, θ j = levTwoS3b_theta.getD j.val 0)
    (D : Finset (Option (Fin (Tag.rank Tag.E8)))) (l : List ℤ) :
    (∃ e : Fin 2, ∃ s : Fin 2,
        (e.val = 0 ∨ (none : Option (Fin (Tag.rank Tag.E8))) ∈ D) ∧
        (∀ j, 0 ≤ (if s.val = 0 then (1 : ℤ) else -1) * l.getD j.val 0 +
          (e.val : ℤ) * θ j) ∧
        (∀ j, (if s.val = 0 then (1 : ℤ) else -1) * l.getD j.val 0 +
          (e.val : ℤ) * θ j ≠ 0 →
            (some j : Option (Fin (Tag.rank Tag.E8))) ∈ D)) ↔
      levTwoS3bK_e8_cond (∑ x ∈ D, 2 ^ f x) l = true := by
  have hinj := levTwoS3bK_e8_idx_injective f h0 hs
  have hb0 : (∑ x ∈ D, 2 ^ f x).testBit 0 = decide (none ∈ D) := by
    rw [← h0]
    exact levTwoS3bK_testBit_sum f hinj D none
  have hbs : ∀ j : Fin (Tag.rank Tag.E8), (∑ x ∈ D, 2 ^ f x).testBit (j.val + 1) = decide (some j ∈ D) := by
    intro j
    rw [← hs j]
    exact levTwoS3bK_testBit_sum f hinj D (some j)
  have hes : ∀ (e : ℕ) (sg : ℤ),
      levTwoS3bK_e8_condES (∑ x ∈ D, 2 ^ f x) l e sg = true ↔
        ((e = 0 ∨ none ∈ D) ∧
          (∀ j : Fin (Tag.rank Tag.E8), 0 ≤ sg * l.getD j.val 0 + (e : ℤ) * θ j) ∧
          (∀ j : Fin (Tag.rank Tag.E8), sg * l.getD j.val 0 + (e : ℤ) * θ j ≠ 0 → some j ∈ D)) := by
    intro e sg
    simp only [levTwoS3bK_e8_condES, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, hb0,
      decide_eq_true_eq, List.all_eq_true, List.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun j => ?_, fun j hj => ?_⟩
      · rw [hθ j]
        exact (h2 j.val j.isLt).1
      · have := (h2 j.val j.isLt).2
        rw [← hθ j] at this
        rw [hbs j] at this
        exact of_decide_eq_true (this.resolve_left hj)
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, fun j hj => ⟨?_, ?_⟩⟩
      · have := h2 ⟨j, hj⟩
        rw [hθ] at this
        exact this
      · have h4 := hbs ⟨j, hj⟩
        have h5 := h3 ⟨j, hj⟩
        rw [hθ] at h5
        by_cases hz : sg * l.getD j 0 + (e : ℤ) * levTwoS3b_theta.getD j 0 = 0
        · exact Or.inl hz
        · right
          rw [h4]
          exact decide_eq_true (h5 hz)
  simp only [levTwoS3bK_e8_cond, Bool.or_eq_true, hes, Fin.exists_fin_two]
  simp only [Fin.val_zero, Fin.val_one, ↓reduceIte, one_ne_zero, Nat.cast_zero, Nat.cast_one,
    Fin.isValue]
  constructor
  · rintro ((h | h) | (h | h))
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · rintro (((h | h) | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

include h0 hs in
theorem levTwoS3bK_e8_block_sound (θ : Fin (Tag.rank Tag.E8) → ℤ)
    (hθ : ∀ j, θ j = levTwoS3b_theta.getD j.val 0) (k : ℕ) (hk : levTwoS3bK_e8_chk k = true)
    (D : Finset (Option (Fin (Tag.rank Tag.E8)))) (hD : (∑ x ∈ D, 2 ^ f x) / 64 = k)
    (hne : D ≠ Finset.univ) (l : List ℤ) (hl : l ∈ Tag.E8.artifactRoots) :
    (∃ e : Fin 2, ∃ s : Fin 2,
        (e.val = 0 ∨ (none : Option (Fin (Tag.rank Tag.E8))) ∈ D) ∧
        (∀ j, 0 ≤ (if s.val = 0 then (1 : ℤ) else -1) * l.getD j.val 0 +
          (e.val : ℤ) * θ j) ∧
        (∀ j, (if s.val = 0 then (1 : ℤ) else -1) * l.getD j.val 0 +
          (e.val : ℤ) * θ j ≠ 0 →
            (some j : Option (Fin (Tag.rank Tag.E8))) ∈ D)) ↔
      levTwoS3b_inPat (∑ x ∈ D, 2 ^ f x) l = true := by
  rw [levTwoS3bK_e8_cond_iff f h0 hs θ hθ D l]
  have huniv : ∑ x : Option (Fin (Tag.rank Tag.E8)), 2 ^ f x = 511 := by
    rw [Fintype.sum_option, h0]
    simp only [hs]
    rfl
  have hlt : ∑ x ∈ D, 2 ^ f x < 511 := by
    obtain ⟨y, hy⟩ : ∃ y, y ∉ D := by
      by_contra h
      exact hne (Finset.eq_univ_of_forall fun y => by_contra fun hy => h ⟨y, hy⟩)
    rw [← huniv]
    exact Finset.sum_lt_sum_of_subset (Finset.subset_univ D) (Finset.mem_univ y) hy
      (Nat.two_pow_pos _) (fun _ _ _ => Nat.zero_le _)
  set m := ∑ x ∈ D, 2 ^ f x
  simp only [levTwoS3bK_e8_chk, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq] at hk
  have hi : m - 64 * k < 64 := by omega
  have hm : 64 * k + (m - 64 * k) = m := by omega
  have hlen : l.length = 8 := length_of_mem_artifactRoots (τ := Tag.E8) hl
  rcases hk (m - 64 * k) hi with h | h
  · omega
  · rw [hm] at h
    rw [← levTwoS3bK_e8_condW_eq m l hlen, h l hl]
