module

public import CFSG.Walter.Ree.Bombieri.SpecComp
public import CFSG.Walter.Ree.Bombieri.Appendix

public section

namespace CFSG.Walter.Ree.Bombieri

namespace Spec

open F3P hiding X
open Polynomial

variable {R : Type*} [CommRing R] (ι : ZMod 3 →+* R) (r : R)

noncomputable def toPolyK : List F3P → R[X]
  | [] => 0
  | a :: l => C (F3P.ev ι r a) + X * toPolyK l

variable {ι r}

@[simp] theorem toPolyK_nil : toPolyK ι r [] = 0 := by rw [toPolyK]

@[simp] theorem toPolyK_cons (a : F3P) (l : List F3P) :
    toPolyK ι r (a :: l) = C (F3P.ev ι r a) + X * toPolyK ι r l := by rw [toPolyK]

@[expose] def AllValid (l : List F3P) : Prop := ∀ a ∈ l, a.Valid

theorem allValid_map_normalize (l : List F3P) : AllValid (l.map normalize) := by
  intro a ha
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
  exact valid_normalize b

theorem AllValid.tail {a : F3P} {l : List F3P} (h : AllValid (a :: l)) : AllValid l :=
  fun b hb => h b (List.mem_cons_of_mem _ hb)

theorem AllValid.head {a : F3P} {l : List F3P} (h : AllValid (a :: l)) : a.Valid :=
  h a (List.mem_cons_self ..)

theorem natDegree_toPolyK_lt : ∀ (l : List F3P), l ≠ [] →
    (toPolyK ι r l).natDegree < l.length
  | [], h => absurd rfl h
  | [a], _ => by simp
  | a :: b :: l, _ => by
    have ih := natDegree_toPolyK_lt (b :: l) (List.cons_ne_nil _ _)
    rw [toPolyK_cons, List.length_cons]
    refine (natDegree_add_le _ _).trans_lt (max_lt (by simp) ?_)
    refine natDegree_mul_le.trans_lt ?_
    have := natDegree_X_le (R := R)
    omega

theorem natDegree_toPolyK_le (l : List F3P) : (toPolyK ι r l).natDegree ≤ l.length - 1 := by
  rcases l with _ | ⟨a, l⟩
  · simp
  · have := natDegree_toPolyK_lt (ι := ι) (r := r) (a :: l) (List.cons_ne_nil _ _)
    simp only [List.length_cons] at this ⊢
    omega

theorem coeff_toPolyK : ∀ (l : List F3P) (i : ℕ),
    (toPolyK ι r l).coeff i = F3P.ev ι r (l.getD i zero)
  | [], i => by simp [ev_zero]
  | a :: l, 0 => by simp
  | a :: l, i + 1 => by
    rw [toPolyK_cons, coeff_add, coeff_C_succ, zero_add, coeff_X_mul, coeff_toPolyK l i]
    simp

theorem sum_map_range {S : Type*} [AddCommMonoid S] (g : ℕ → S) (n : ℕ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

theorem prod_map_range {S : Type*} [CommMonoid S] (g : ℕ → S) (n : ℕ) :
    ((List.range n).map g).prod = ∏ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.prod_append, ih,
      Finset.prod_range_succ]; simp

section

variable {T : Tab} (hm : PE.IsMul ι r (mulT T))
include hm

omit hm in
theorem sumL_spec : ∀ {l : List F3P}, AllValid l →
    (sumL l).Valid ∧ F3P.ev ι r (sumL l) = (l.map (F3P.ev ι r)).sum := by
  suffices h : ∀ (l : List F3P) (acc : F3P), acc.Valid → AllValid l →
      (l.foldl add acc).Valid ∧
        F3P.ev ι r (l.foldl add acc) = F3P.ev ι r acc + (l.map (F3P.ev ι r)).sum by
    intro l hl
    obtain ⟨h1, h2⟩ := h l zero valid_zero hl
    exact ⟨h1, by rw [sumL, h2, ev_zero, zero_add]⟩
  intro l
  induction l with
  | nil => intro acc hacc _; simpa using hacc
  | cons a l ih =>
    intro acc hacc hl
    obtain ⟨h1, h2⟩ := ih (add acc a) (valid_add hacc hl.head) hl.tail
    refine ⟨by simpa using h1, ?_⟩
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [h2, ev_add hacc hl.head, add_assoc]

theorem prodT_spec : ∀ {l : List F3P}, AllValid l →
    (prodT T l).Valid ∧ F3P.ev ι r (prodT T l) = (l.map (F3P.ev ι r)).prod := by
  suffices h : ∀ (l : List F3P) (acc : F3P), acc.Valid → AllValid l →
      (l.foldl (mulT T) acc).Valid ∧
        F3P.ev ι r (l.foldl (mulT T) acc) = F3P.ev ι r acc * (l.map (F3P.ev ι r)).prod by
    intro l hl
    obtain ⟨h1, h2⟩ := h l one valid_one hl
    exact ⟨h1, by rw [prodT, h2, ev_one, one_mul]⟩
  intro l
  induction l with
  | nil => intro acc hacc _; simpa using hacc
  | cons a l ih =>
    intro acc hacc hl
    obtain ⟨hv, he⟩ := hm acc a hacc hl.head
    obtain ⟨h1, h2⟩ := ih (mulT T acc a) hv hl.tail
    refine ⟨by simpa using h1, ?_⟩
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    rw [h2, he, mul_assoc]

theorem horner_spec {x : F3P} (hx : x.Valid) : ∀ {l : List F3P}, AllValid l →
    (horner T l x).Valid ∧ F3P.ev ι r (horner T l x) = (toPolyK ι r l).eval (F3P.ev ι r x)
  | [], _ => ⟨valid_zero, by simp [horner, ev_zero]⟩
  | a :: l, h => by
    obtain ⟨h1, h2⟩ := horner_spec hx h.tail
    obtain ⟨h3, h4⟩ := hm x _ hx h1
    refine ⟨valid_add h.head h3, ?_⟩
    rw [horner, ev_add h.head h3, h4, h2]
    simp

end

end Spec

end CFSG.Walter.Ree.Bombieri
