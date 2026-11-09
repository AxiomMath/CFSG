module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Zip

public section

namespace CFSG.Decide.FinFun

@[expose] def allFns {α : Type*} (l : List α) : (n : ℕ) → List (Fin n → α)
  | 0 => [Fin.elim0]
  | n + 1 => l.flatMap fun a => (allFns l n).map fun f => Fin.cons a f

theorem mem_allFns {α : Type*} {l : List α} (hl : ∀ a, a ∈ l) :
    ∀ (n : ℕ) (f : Fin n → α), f ∈ allFns l n
  | 0, f => by
    have : f = Fin.elim0 := funext fun i => i.elim0
    simp [allFns, this]
  | n + 1, f => by
    rw [allFns, List.mem_flatMap]
    refine ⟨f 0, hl _, List.mem_map.2 ⟨Fin.tail f, mem_allFns hl n _, Fin.cons_self_tail f⟩⟩

@[expose, instance_reducible] def decForall {α : Type*} (l : List α) (hl : ∀ a, a ∈ l) (n : ℕ) (P : (Fin n → α) → Prop)
    [DecidablePred P] : Decidable (∀ f, P f) :=
  decidable_of_iff (∀ f ∈ allFns l n, P f)
    ⟨fun h f => h f (mem_allFns hl n f), fun h f _ => h f⟩

@[expose, instance_reducible] def decExists {α : Type*} (l : List α) (hl : ∀ a, a ∈ l) (n : ℕ) (P : (Fin n → α) → Prop)
    [DecidablePred P] : Decidable (∃ f, P f) :=
  decidable_of_iff (∃ f ∈ allFns l n, P f)
    ⟨fun ⟨f, _, h⟩ => ⟨f, h⟩, fun ⟨f, h⟩ => ⟨f, mem_allFns hl n f, h⟩⟩

@[expose, instance_reducible] def decEq {α : Type*} [DecidableEq α] (n : ℕ) : DecidableEq (Fin n → α) := fun f g =>
  decidable_of_iff (∀ i ∈ List.finRange n, f i = g i)
    ⟨fun h => funext fun i => h i (List.mem_finRange i), fun h _ _ => h ▸ rfl⟩

theorem mem_zmod3 : ∀ a : ZMod 3, a ∈ ([0, 1, 2] : List (ZMod 3)) := by decide
theorem mem_zmod2 : ∀ a : ZMod 2, a ∈ ([0, 1] : List (ZMod 2)) := by decide

@[expose, instance_reducible] def decForallZ3 (n : ℕ) (P : (Fin n → ZMod 3) → Prop) [DecidablePred P] : Decidable (∀ f, P f) :=
  decForall [0, 1, 2] mem_zmod3 n P
@[expose, instance_reducible] def decExistsZ3 (n : ℕ) (P : (Fin n → ZMod 3) → Prop) [DecidablePred P] : Decidable (∃ f, P f) :=
  decExists [0, 1, 2] mem_zmod3 n P
@[expose, instance_reducible] def decForallZ2 (n : ℕ) (P : (Fin n → ZMod 2) → Prop) [DecidablePred P] : Decidable (∀ f, P f) :=
  decForall [0, 1] mem_zmod2 n P
@[expose, instance_reducible] def decExistsZ2 (n : ℕ) (P : (Fin n → ZMod 2) → Prop) [DecidablePred P] : Decidable (∃ f, P f) :=
  decExists [0, 1] mem_zmod2 n P

theorem forall_of_forall_cons {α : Type*} {n : ℕ} {P : (Fin (n + 1) → α) → Prop}
    (h : ∀ (a : α) (w : Fin n → α), P (Fin.cons a w)) : ∀ v, P v := by
  intro v
  have := h (v 0) (Fin.tail v)
  rwa [Fin.cons_self_tail] at this

theorem forall_of_forall_cons_cons {α : Type*} {n : ℕ} {P : (Fin (n + 2) → α) → Prop}
    (h : ∀ (a b : α) (w : Fin n → α), P (Fin.cons a (Fin.cons b w))) : ∀ v, P v :=
  forall_of_forall_cons fun a => forall_of_forall_cons fun b w => h a b w

theorem zmod3_cases {P : ZMod 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ a, P a := by
  intro a
  have := mem_zmod3 a
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl <;> assumption

theorem zmod3_eq_two {a : ZMod 3} (h0 : a ≠ 0) (h1 : a ≠ 1) : a = 2 := by
  revert a
  decide

theorem zmod2_cases {P : ZMod 2 → Prop} (h0 : P 0) (h1 : P 1) : ∀ a, P a := by
  intro a
  have := mem_zmod2 a
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl <;> assumption

theorem zmod3_three (a : ZMod 3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  revert a
  decide

theorem zmod5_ne_zero {a : ZMod 5} (h : a ≠ 0) : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by
  revert a
  decide

theorem all_range_of_chunks {f : ℕ → Bool} {n s : ℕ} (c : ℕ) (hn : n ≤ c * s)
    (h : ∀ i < c, (List.range' (i * s) s).all f = true) : (List.range n).all f = true := by
  rw [List.all_eq_true]
  intro x hx
  have hx' := List.mem_range.1 hx
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs; omega
    · exact hs
  have hi : x / s < c := (Nat.div_lt_iff_lt_mul hs).2 (by omega)
  have hc := List.all_eq_true.1 (h (x / s) hi) x
  apply hc
  rw [List.mem_range'_1]
  have h1 := Nat.div_mul_le_self x s
  have h2 := Nat.lt_div_mul_add (a := x) hs
  constructor <;> omega

theorem all_of_chunks {α : Type*} {f : α → Bool} (s : ℕ) :
    ∀ (c : ℕ) (l : List α), l.length ≤ c * s →
      (∀ k < c, ((l.drop (k * s)).take s).all f = true) → l.all f = true
  | 0, l, hl, _ => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [this]
  | c + 1, l, hl, h => by
    rw [← List.take_append_drop s l, List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), all_of_chunks s c (l.drop s) ?_ fun k hk => ?_⟩
    · simp only [List.length_drop]; rw [Nat.add_mul] at hl; omega
    · have := h (k + 1) (by omega)
      rwa [List.drop_drop, show s + k * s = (k + 1) * s by rw [Nat.add_mul, Nat.one_mul,
        Nat.add_comm]]

theorem all_mem_of_witness {α β : Type*} [DecidableEq β] (G : List α) (S : List β)
    (f : α → β → β) (W : List (List ℕ)) (d : β) (hW : W.length = S.length)
    (hWr : (W.all fun r => r.length == G.length) = true)
    (h : ((S.zip W).all fun p => (G.zip p.2).all fun q =>
      decide (q.2 < S.length) && decide (S.getD q.2 d = f q.1 p.1)) = true) :
    (G.all fun g => S.all fun v => decide (f g v ∈ S)) = true := by
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h hWr ⊢
  intro g hg v hv
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hv
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
  have hkW : k < W.length := by omega
  have hrow : (W[k]'hkW).length = G.length := hWr _ (List.getElem_mem _)
  have hp : (S[k], W[k]'hkW) ∈ S.zip W := by
    rw [List.mem_iff_getElem]
    exact ⟨k, by simp only [List.length_zip]; omega, by simp⟩
  have hq : (G[j], (W[k]'hkW)[j]'(by omega)) ∈ G.zip (W[k]'hkW) := by
    rw [List.mem_iff_getElem]
    exact ⟨j, by simp only [List.length_zip]; omega, by simp⟩
  obtain ⟨hlt, heq⟩ := h _ hp _ hq
  simp only at hlt heq
  rw [← heq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  exact List.getElem_mem _

theorem all_mem_of_witnessN {α β : Type*} [DecidableEq β] (G : List α) (S : List β)
    (f : α → β → β) (W : List (List ℕ)) (d : β) (N : ℕ) (hN : S.length = N)
    (hW : W.length = S.length)
    (hWr : (W.all fun r => r.length == G.length) = true)
    (h : ((S.zip W).all fun p => (G.zip p.2).all fun q =>
      decide (q.2 < N) && decide (S.getD q.2 d = f q.1 p.1)) = true) :
    (G.all fun g => S.all fun v => decide (f g v ∈ S)) = true := by
  subst hN
  exact all_mem_of_witness G S f W d hW hWr h

end CFSG.Decide.FinFun

end
