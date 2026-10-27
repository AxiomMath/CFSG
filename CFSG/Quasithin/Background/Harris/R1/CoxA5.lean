module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.Quasithin.Background.Harris.R1.CoxA5

@[expose] def covR : List (List Bool × List Bool) :=
  [([true, true], []),
   ([false, false, false], []),
   ([true, false, true, false, true, false, true, false, true, false], []),
   ([false, true, false, true, false, true], [true, false, false, true, false, false]),
   ([false, false, true, false, false, true], [true, false, true, false, true, false]),
   ([false, true, false, true, false, false, true, false, true, false], [true, false, false, true, false, true, false, false, true]),
   ([false, false, true, false, true, false, false, true, false, false], [true, false, true, false, true, false, false, true, false, true]),
   ([false, true, false, false, true, false, true, false, false, true, false, true], [true, false, true, false, false, true, false, true, false, false, true, false])]

@[expose] def covNf : List (List Bool) :=
  [[],
   [true],
   [false],
   [true, false],
   [false, true],
   [false, false],
   [true, false, true],
   [true, false, false],
   [false, true, false],
   [false, false, true],
   [true, false, true, false],
   [true, false, false, true],
   [false, true, false, true],
   [false, true, false, false],
   [false, false, true, false],
   [true, false, true, false, true],
   [true, false, true, false, false],
   [true, false, false, true, false],
   [false, true, false, true, false],
   [false, true, false, false, true],
   [false, false, true, false, true],
   [false, false, true, false, false],
   [true, false, true, false, true, false],
   [true, false, true, false, false, true],
   [true, false, false, true, false, true],
   [true, false, false, true, false, false],
   [false, true, false, true, false, false],
   [false, true, false, false, true, false],
   [false, false, true, false, true, false],
   [true, false, true, false, true, false, false],
   [true, false, true, false, false, true, false],
   [true, false, false, true, false, true, false],
   [false, true, false, true, false, false, true],
   [false, true, false, false, true, false, true],
   [false, true, false, false, true, false, false],
   [false, false, true, false, true, false, false],
   [true, false, true, false, true, false, false, true],
   [true, false, true, false, false, true, false, true],
   [true, false, true, false, false, true, false, false],
   [true, false, false, true, false, true, false, false],
   [false, true, false, true, false, false, true, false],
   [false, true, false, false, true, false, true, false],
   [false, false, true, false, true, false, false, true],
   [true, false, true, false, true, false, false, true, false],
   [true, false, true, false, false, true, false, true, false],
   [true, false, false, true, false, true, false, false, true],
   [false, true, false, true, false, false, true, false, true],
   [false, true, false, true, false, false, true, false, false],
   [false, true, false, false, true, false, true, false, false],
   [false, false, true, false, true, false, false, true, false],
   [true, false, true, false, true, false, false, true, false, true],
   [true, false, true, false, true, false, false, true, false, false],
   [true, false, true, false, false, true, false, true, false, false],
   [true, false, false, true, false, true, false, false, true, false],
   [false, true, false, false, true, false, true, false, false, true],
   [false, false, true, false, true, false, false, true, false, true],
   [true, false, true, false, false, true, false, true, false, false, true],
   [true, false, false, true, false, true, false, false, true, false, true],
   [false, true, false, false, true, false, true, false, false, true, false],
   [true, false, true, false, false, true, false, true, false, false, true, false]]

@[expose] def covChain3 : List (ℕ × ℕ × Bool) := [(0, 0, true), (1, 1, true), (3, 0, true), (13, 1, true), (4, 2, false)]

@[expose] def covChain4 : List (ℕ × ℕ × Bool) := [(0, 0, true), (1, 3, true), (6, 0, false)]

@[expose] def covChain5 : List (ℕ × ℕ × Bool) := [(0, 0, true), (1, 4, true), (5, 3, false), (9, 1, false)]

@[expose] def covChain6 : List (ℕ × ℕ × Bool) := [(4, 3, true), (0, 4, false)]

@[expose] def covChain7 : List (ℕ × ℕ × Bool) := [(3, 0, true), (4, 6, true), (0, 5, false), (2, 5, false)]

@[expose] def covTable : List (List Bool × Bool × List (ℕ × ℕ × Bool) × List Bool) :=
  [([], true, [], [true]),
   ([], false, [], [false]),
   ([true], true, [(0, 0, false)], []),
   ([true], false, [], [false, true]),
   ([false], true, [], [true, false]),
   ([false], false, [], [false, false]),
   ([true, false], true, [(0, 0, false)], [false]),
   ([true, false], false, [], [false, true, false]),
   ([false, true], true, [], [true, false, true]),
   ([false, true], false, [], [false, false, true]),
   ([false, false], true, [], [true, false, false]),
   ([false, false], false, [(0, 1, false)], []),
   ([true, false, true], true, [(0, 0, false)], [false, true]),
   ([true, false, true], false, [], [false, true, false, true]),
   ([true, false, false], true, [(0, 0, false)], [false, false]),
   ([true, false, false], false, [], [false, true, false, false]),
   ([false, true, false], true, [], [true, false, true, false]),
   ([false, true, false], false, [], [false, false, true, false]),
   ([false, false, true], true, [], [true, false, false, true]),
   ([false, false, true], false, [(0, 1, false)], [true]),
   ([true, false, true, false], true, [(0, 0, false)], [false, true, false]),
   ([true, false, true, false], false, [], [false, true, false, true, false]),
   ([true, false, false, true], true, [(0, 0, false)], [false, false, true]),
   ([true, false, false, true], false, [], [false, true, false, false, true]),
   ([false, true, false, true], true, [], [true, false, true, false, true]),
   ([false, true, false, true], false, [], [false, false, true, false, true]),
   ([false, true, false, false], true, [], [true, false, true, false, false]),
   ([false, true, false, false], false, [], [false, false, true, false, false]),
   ([false, false, true, false], true, [], [true, false, false, true, false]),
   ([false, false, true, false], false, [(0, 1, false)], [true, false]),
   ([true, false, true, false, true], true, [(0, 0, false)], [false, true, false, true]),
   ([true, false, true, false, true], false, [(0, 3, false)], [true, false, false, true, false, false]),
   ([true, false, true, false, false], true, [(0, 0, false)], [false, true, false, false]),
   ([true, false, true, false, false], false, [], [false, true, false, true, false, false]),
   ([true, false, false, true, false], true, [(0, 0, false)], [false, false, true, false]),
   ([true, false, false, true, false], false, [], [false, true, false, false, true, false]),
   ([false, true, false, true, false], true, [], [true, false, true, false, true, false]),
   ([false, true, false, true, false], false, [], [false, false, true, false, true, false]),
   ([false, true, false, false, true], true, [], [true, false, true, false, false, true]),
   ([false, true, false, false, true], false, [(0, 4, false)], [true, false, true, false, true, false]),
   ([false, false, true, false, true], true, [], [true, false, false, true, false, true]),
   ([false, false, true, false, true], false, [(0, 1, false)], [true, false, true]),
   ([false, false, true, false, false], true, [], [true, false, false, true, false, false]),
   ([false, false, true, false, false], false, [(0, 1, false)], [true, false, false]),
   ([true, false, true, false, true, false], true, [(0, 0, false)], [false, true, false, true, false]),
   ([true, false, true, false, true, false], false, [(0, 3, false), (4, 1, false)], [true, false, false, true]),
   ([true, false, true, false, false, true], true, [(0, 0, false)], [false, true, false, false, true]),
   ([true, false, true, false, false, true], false, [], [false, true, false, true, false, false, true]),
   ([true, false, false, true, false, true], true, [(0, 0, false)], [false, false, true, false, true]),
   ([true, false, false, true, false, true], false, [], [false, true, false, false, true, false, true]),
   ([true, false, false, true, false, false], true, [(0, 0, false)], [false, false, true, false, false]),
   ([true, false, false, true, false, false], false, [], [false, true, false, false, true, false, false]),
   ([false, true, false, true, false, false], true, [], [true, false, true, false, true, false, false]),
   ([false, true, false, true, false, false], false, [], [false, false, true, false, true, false, false]),
   ([false, true, false, false, true, false], true, [], [true, false, true, false, false, true, false]),
   ([false, true, false, false, true, false], false, [(0, 4, false)], [true, false, true, false, true, false, false]),
   ([false, false, true, false, true, false], true, [], [true, false, false, true, false, true, false]),
   ([false, false, true, false, true, false], false, [(0, 1, false)], [true, false, true, false]),
   ([true, false, true, false, true, false, false], true, [(0, 0, false)], [false, true, false, true, false, false]),
   ([true, false, true, false, true, false, false], false, [(0, 3, false), (4, 1, false)], [true, false, false, true, false]),
   ([true, false, true, false, false, true, false], true, [(0, 0, false)], [false, true, false, false, true, false]),
   ([true, false, true, false, false, true, false], false, [], [false, true, false, true, false, false, true, false]),
   ([true, false, false, true, false, true, false], true, [(0, 0, false)], [false, false, true, false, true, false]),
   ([true, false, false, true, false, true, false], false, [], [false, true, false, false, true, false, true, false]),
   ([false, true, false, true, false, false, true], true, [], [true, false, true, false, true, false, false, true]),
   ([false, true, false, true, false, false, true], false, [], [false, false, true, false, true, false, false, true]),
   ([false, true, false, false, true, false, true], true, [], [true, false, true, false, false, true, false, true]),
   ([false, true, false, false, true, false, true], false, [(0, 4, false)], [true, false, true, false, true, false, false, true]),
   ([false, true, false, false, true, false, false], true, [], [true, false, true, false, false, true, false, false]),
   ([false, true, false, false, true, false, false], false, [(0, 4, false), (5, 1, false)], [true, false, true, false, true]),
   ([false, false, true, false, true, false, false], true, [], [true, false, false, true, false, true, false, false]),
   ([false, false, true, false, true, false, false], false, [(0, 1, false)], [true, false, true, false, false]),
   ([true, false, true, false, true, false, false, true], true, [(0, 0, false)], [false, true, false, true, false, false, true]),
   ([true, false, true, false, true, false, false, true], false, [(0, 3, false), (4, 1, false)], [true, false, false, true, false, true]),
   ([true, false, true, false, false, true, false, true], true, [(0, 0, false)], [false, true, false, false, true, false, true]),
   ([true, false, true, false, false, true, false, true], false, [], [false, true, false, true, false, false, true, false, true]),
   ([true, false, true, false, false, true, false, false], true, [(0, 0, false)], [false, true, false, false, true, false, false]),
   ([true, false, true, false, false, true, false, false], false, [], [false, true, false, true, false, false, true, false, false]),
   ([true, false, false, true, false, true, false, false], true, [(0, 0, false)], [false, false, true, false, true, false, false]),
   ([true, false, false, true, false, true, false, false], false, [], [false, true, false, false, true, false, true, false, false]),
   ([false, true, false, true, false, false, true, false], true, [], [true, false, true, false, true, false, false, true, false]),
   ([false, true, false, true, false, false, true, false], false, [], [false, false, true, false, true, false, false, true, false]),
   ([false, true, false, false, true, false, true, false], true, [], [true, false, true, false, false, true, false, true, false]),
   ([false, true, false, false, true, false, true, false], false, [(0, 4, false)], [true, false, true, false, true, false, false, true, false]),
   ([false, false, true, false, true, false, false, true], true, [], [true, false, false, true, false, true, false, false, true]),
   ([false, false, true, false, true, false, false, true], false, [(0, 1, false)], [true, false, true, false, false, true]),
   ([true, false, true, false, true, false, false, true, false], true, [(0, 0, false)], [false, true, false, true, false, false, true, false]),
   ([true, false, true, false, true, false, false, true, false], false, [(0, 3, false), (4, 1, false)], [true, false, false, true, false, true, false]),
   ([true, false, true, false, false, true, false, true, false], true, [(0, 0, false)], [false, true, false, false, true, false, true, false]),
   ([true, false, true, false, false, true, false, true, false], false, [(0, 5, false)], [true, false, false, true, false, true, false, false, true]),
   ([true, false, false, true, false, true, false, false, true], true, [(0, 0, false)], [false, false, true, false, true, false, false, true]),
   ([true, false, false, true, false, true, false, false, true], false, [], [false, true, false, false, true, false, true, false, false, true]),
   ([false, true, false, true, false, false, true, false, true], true, [], [true, false, true, false, true, false, false, true, false, true]),
   ([false, true, false, true, false, false, true, false, true], false, [], [false, false, true, false, true, false, false, true, false, true]),
   ([false, true, false, true, false, false, true, false, false], true, [], [true, false, true, false, true, false, false, true, false, false]),
   ([false, true, false, true, false, false, true, false, false], false, [(0, 6, false)], [true, false, true, false, true, false, false, true, false, true]),
   ([false, true, false, false, true, false, true, false, false], true, [], [true, false, true, false, false, true, false, true, false, false]),
   ([false, true, false, false, true, false, true, false, false], false, [(0, 4, false)], [true, false, true, false, true, false, false, true, false, false]),
   ([false, false, true, false, true, false, false, true, false], true, [], [true, false, false, true, false, true, false, false, true, false]),
   ([false, false, true, false, true, false, false, true, false], false, [(0, 1, false)], [true, false, true, false, false, true, false]),
   ([true, false, true, false, true, false, false, true, false, true], true, [(0, 0, false)], [false, true, false, true, false, false, true, false, true]),
   ([true, false, true, false, true, false, false, true, false, true], false, [(0, 3, false), (4, 1, false), (2, 3, false)], [true, false, true, false, false, true, false, false]),
   ([true, false, true, false, true, false, false, true, false, false], true, [(0, 0, false)], [false, true, false, true, false, false, true, false, false]),
   ([true, false, true, false, true, false, false, true, false, false], false, [(0, 3, false), (4, 1, false)], [true, false, false, true, false, true, false, false]),
   ([true, false, true, false, false, true, false, true, false, false], true, [(0, 0, false)], [false, true, false, false, true, false, true, false, false]),
   ([true, false, true, false, false, true, false, true, false, false], false, [(0, 5, false)], [true, false, false, true, false, true, false, false, true, false]),
   ([true, false, false, true, false, true, false, false, true, false], true, [(0, 0, false)], [false, false, true, false, true, false, false, true, false]),
   ([true, false, false, true, false, true, false, false, true, false], false, [], [false, true, false, false, true, false, true, false, false, true, false]),
   ([false, true, false, false, true, false, true, false, false, true], true, [], [true, false, true, false, false, true, false, true, false, false, true]),
   ([false, true, false, false, true, false, true, false, false, true], false, [(0, 4, false), (5, 4, false), (4, 0, false)], [true, false, true, false, false, true, false, true, false]),
   ([false, false, true, false, true, false, false, true, false, true], true, [], [true, false, false, true, false, true, false, false, true, false, true]),
   ([false, false, true, false, true, false, false, true, false, true], false, [(0, 1, false)], [true, false, true, false, false, true, false, true]),
   ([true, false, true, false, false, true, false, true, false, false, true], true, [(0, 0, false)], [false, true, false, false, true, false, true, false, false, true]),
   ([true, false, true, false, false, true, false, true, false, false, true], false, [(0, 5, false)], [true, false, false, true, false, true, false, false, true, false, true]),
   ([true, false, false, true, false, true, false, false, true, false, true], true, [(0, 0, false)], [false, false, true, false, true, false, false, true, false, true]),
   ([true, false, false, true, false, true, false, false, true, false, true], false, [(0, 7, false)], [true, false, true, false, false, true, false, true, false, false, true, false]),
   ([false, true, false, false, true, false, true, false, false, true, false], true, [], [true, false, true, false, false, true, false, true, false, false, true, false]),
   ([false, true, false, false, true, false, true, false, false, true, false], false, [(0, 4, false), (5, 4, false), (4, 0, false)], [true, false, true, false, false, true, false, true, false, false]),
   ([true, false, true, false, false, true, false, true, false, false, true, false], true, [(0, 0, false)], [false, true, false, false, true, false, true, false, false, true, false]),
   ([true, false, true, false, false, true, false, true, false, false, true, false], false, [(0, 5, false), (2, 5, false)], [true, false, true, false, false, true, false, true, false, false, true])]


variable {H : Type*} [Group H] (a b : H)

@[expose] def eval (w : List Bool) : H := (w.map fun c => if c then a else b).prod

theorem eval_append (p q : List Bool) : eval a b (p ++ q) = eval a b p * eval a b q := by
  simp [eval, List.prod_append]

@[expose] def step (Rs : List (List Bool × List Bool)) (w : List Bool) (m : ℕ × ℕ × Bool) :
    Option (List Bool) :=
  match Rs[m.2.1]? with
  | none => none
  | some (l, r) =>
    if (w.drop m.1).take (if m.2.2 then r else l).length = (if m.2.2 then r else l) then
      some (w.take m.1 ++ (if m.2.2 then l else r) ++ w.drop (m.1 + (if m.2.2 then r else l).length))
    else none

@[expose] def run (Rs : List (List Bool × List Bool)) :
    List Bool → List (ℕ × ℕ × Bool) → Option (List Bool)
  | w, [] => some w
  | w, m :: ms =>
    match step Rs w m with
    | none => none
    | some w' => run Rs w' ms

theorem split_at (w x : List Bool) (i : ℕ) (h : (w.drop i).take x.length = x) :
    w = w.take i ++ x ++ w.drop (i + x.length) := by
  calc w = w.take i ++ w.drop i := (List.take_append_drop i w).symm
    _ = w.take i ++ ((w.drop i).take x.length ++ (w.drop i).drop x.length) := by
        rw [List.take_append_drop x.length (w.drop i), List.take_append_drop]
    _ = _ := by rw [h, List.drop_drop, List.append_assoc]

theorem eval_rewrite {x y : List Bool} (hxy : eval a b x = eval a b y) {w : List Bool} {i : ℕ}
    (h : (w.drop i).take x.length = x) :
    eval a b w = eval a b (w.take i ++ y ++ w.drop (i + x.length)) := by
  calc eval a b w = eval a b (w.take i ++ x ++ w.drop (i + x.length)) :=
        congrArg (eval a b) (split_at w x i h)
    _ = _ := by rw [eval_append, eval_append, eval_append, eval_append, hxy]

theorem eval_step {Rs : List (List Bool × List Bool)}
    (hR : ∀ p ∈ Rs, eval a b p.1 = eval a b p.2) {w : List Bool} {m : ℕ × ℕ × Bool}
    {w' : List Bool} (h : step Rs w m = some w') : eval a b w = eval a b w' := by
  unfold step at h
  rcases hk : Rs[m.2.1]? with _ | ⟨l, r⟩
  · rw [hk] at h; simp at h
  · rw [hk] at h
    have hmem : (l, r) ∈ Rs := List.mem_of_getElem? hk
    have hv : eval a b l = eval a b r := hR _ hmem
    by_cases hd : m.2.2 = true
    · simp only [hd, ite_true] at h
      split_ifs at h with hc
      · injection h with h
        subst h
        exact eval_rewrite a b hv.symm hc
    · simp only [hd, ite_false, Bool.false_eq_true] at h
      split_ifs at h with hc
      · injection h with h
        subst h
        exact eval_rewrite a b hv hc

theorem eval_run {Rs : List (List Bool × List Bool)}
    (hR : ∀ p ∈ Rs, eval a b p.1 = eval a b p.2) :
    ∀ (ms : List (ℕ × ℕ × Bool)) {w w' : List Bool}, run Rs w ms = some w' →
      eval a b w = eval a b w' := by
  intro ms
  induction ms with
  | nil => intro w w' h; simp [run] at h; rw [h]
  | cons m ms ih =>
    intro w w' h
    unfold run at h
    rcases hs : step Rs w m with _ | w₁
    · rw [hs] at h; simp at h
    · rw [hs] at h
      exact (eval_step a b hR hs).trans (ih h)

theorem valid_extend (k : ℕ) (chain : List (ℕ × ℕ × Bool))
    (hprev : ∀ p ∈ covR.take k, eval a b p.1 = eval a b p.2)
    (hc : run (covR.take k) (covR.getD k ([], [])).1 chain = some (covR.getD k ([], [])).2) :
    ∀ p ∈ covR.take (k + 1), eval a b p.1 = eval a b p.2 := by
  intro p hp
  rw [List.take_add_one] at hp
  rcases List.mem_append.mp hp with h | h
  · exact hprev p h
  · have hp' : p = covR.getD k ([], []) := by
      cases hk : covR[k]? with
      | none => rw [hk] at h; simp at h
      | some q =>
        rw [hk] at h
        simp at h
        rw [h, List.getD_eq_getElem?_getD, hk]; rfl
    rw [hp']
    exact eval_run a b hprev chain hc

theorem rules_valid (ha : a * a = 1) (hb : b * b * b = 1) (hab : (a * b) ^ 5 = 1) :
    ∀ p ∈ covR, eval a b p.1 = eval a b p.2 := by
  have h0 : ∀ p ∈ covR.take 3, eval a b p.1 = eval a b p.2 := by
    intro p hp
    simp only [covR, List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl | rfl
    · simpa [eval] using ha
    · simpa [eval, mul_assoc] using hb
    · simpa [eval, mul_assoc, pow_succ] using hab
  have h1 := valid_extend a b 3 covChain3 h0 (by decide)
  have h2 := valid_extend a b 4 covChain4 h1 (by decide)
  have h3 := valid_extend a b 5 covChain5 h2 (by decide)
  have h4 := valid_extend a b 6 covChain6 h3 (by decide)
  have h5 := valid_extend a b 7 covChain7 h4 (by decide)
  intro p hp
  exact h5 p (by simpa [covR] using hp)

theorem table_ok : ∀ t ∈ covTable, run covR (t.2.1 :: t.1) t.2.2.1 = some t.2.2.2 := by
  decide +kernel

theorem table_nf : ∀ t ∈ covTable, t.2.2.2 ∈ covNf := by decide +kernel

theorem table_complete : ∀ w ∈ covNf, ∀ g : Bool, ∃ t ∈ covTable, t.1 = w ∧ t.2.1 = g := by
  decide +kernel

theorem nil_mem_covNf : ([] : List Bool) ∈ covNf := by decide

theorem covNf_length : covNf.length = 60 := by decide

theorem closure_words (ha : a * a = 1) (hb : b * b * b = 1) (hab : (a * b) ^ 5 = 1) :
    ∀ x ∈ Subgroup.closure ({a, b} : Set H), ∃ w ∈ covNf, eval a b w = x := by
  have hv := rules_valid a b ha hb hab
  have hleft : ∀ (g : Bool) (y : H), (∃ w ∈ covNf, eval a b w = y) →
      ∃ w ∈ covNf, eval a b w = (if g then a else b) * y := by
    rintro g y ⟨w, hw, rfl⟩
    obtain ⟨t, ht, h1, h2⟩ := table_complete w hw g
    refine ⟨t.2.2.2, table_nf t ht, ?_⟩
    have := eval_run a b hv t.2.2.1 (table_ok t ht)
    rw [← this, h2, h1]
    simp [eval]
  intro x hx
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨[], nil_mem_covNf, by simp [eval]⟩
  | mul_left x hx y _ ih =>
    rcases hx with rfl | hx
    · simpa using hleft true y ih
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      simpa using hleft false y ih
  | inv_mul_cancel x hx y _ ih =>
    rcases hx with rfl | hx
    · rw [inv_eq_of_mul_eq_one_right ha]
      simpa using hleft true y ih
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hb : x * (x * x) = 1)]
      have h1 := hleft false y ih
      have h2 := hleft false _ h1
      simpa [mul_assoc] using h2

end CFSG.Quasithin.Background.Harris.R1.CoxA5
