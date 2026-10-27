module

public import CFSG.GroupActions.ExchangeCoxeter

public section

namespace CFSG.Monster.B.Geometry

open CFSG.GroupActions.Exchange

structure BraidMove (B : Type*) where
  pre : List B
  s : B
  t : B
  len : ℕ
  suf : List B

namespace BraidMove

variable {B : Type*}

@[expose] def source (e : BraidMove B) : List B := e.pre ++ altWord e.s e.t e.len ++ e.suf

@[expose] def target (e : BraidMove B) : List B := e.pre ++ altWord e.t e.s e.len ++ e.suf

@[expose] def reverse (e : BraidMove B) : BraidMove B := ⟨e.pre, e.t, e.s, e.len, e.suf⟩

@[expose] def extend (α β : List B) (e : BraidMove B) : BraidMove B :=
  ⟨α ++ e.pre, e.s, e.t, e.len, e.suf ++ β⟩

@[expose] def IsValid (m : B → B → ℕ) (e : BraidMove B) : Prop :=
  e.s ≠ e.t ∧ e.len = m e.s e.t ∧ e.len ≠ 0

@[simp] theorem reverse_reverse (e : BraidMove B) : e.reverse.reverse = e := rfl

@[simp] theorem source_reverse (e : BraidMove B) : e.reverse.source = e.target := rfl

@[simp] theorem target_reverse (e : BraidMove B) : e.reverse.target = e.source := rfl

theorem source_extend (α β : List B) (e : BraidMove B) :
    (e.extend α β).source = α ++ e.source ++ β := by
  simp [source, extend, List.append_assoc]

theorem target_extend (α β : List B) (e : BraidMove B) :
    (e.extend α β).target = α ++ e.target ++ β := by
  simp [target, extend, List.append_assoc]

@[simp] theorem reverse_extend (α β : List B) (e : BraidMove B) :
    (e.extend α β).reverse = e.reverse.extend α β := rfl

theorem extend_extend (α β α' β' : List B) (e : BraidMove B) :
    (e.extend α β).extend α' β' = e.extend (α' ++ α) (β ++ β') := by
  simp [extend, List.append_assoc]

@[simp] theorem extend_nil_nil (e : BraidMove B) : e.extend [] [] = e := by
  simp [extend]

theorem extend_comp_extend (α β α' β' : List B) :
    BraidMove.extend α' β' ∘ BraidMove.extend α β = BraidMove.extend (α' ++ α) (β ++ β') :=
  funext fun e => extend_extend α β α' β' e

theorem length_target (e : BraidMove B) : e.target.length = e.source.length := by
  simp [source, target]

theorem IsValid.reverse {m : B → B → ℕ} (hm : ∀ a b, m a b = m b a) {e : BraidMove B}
    (he : e.IsValid m) : e.reverse.IsValid m :=
  ⟨he.1.symm, he.2.1.trans (hm _ _), he.2.2⟩

theorem IsValid.extend {m : B → B → ℕ} {e : BraidMove B} (he : e.IsValid m) (α β : List B) :
    (e.extend α β).IsValid m :=
  he

end BraidMove

variable {B : Type*} {m : B → B → ℕ}

@[expose] def IsBraidPath (m : B → B → ℕ) : List B → List (BraidMove B) → List B → Prop
  | x, [], y => x = y
  | x, e :: γ, y => e.IsValid m ∧ e.source = x ∧ IsBraidPath m e.target γ y

@[simp] theorem isBraidPath_nil {x y : List B} : IsBraidPath m x [] y ↔ x = y := Iff.rfl

theorem isBraidPath_cons {x y : List B} {e : BraidMove B} {γ : List (BraidMove B)} :
    IsBraidPath m x (e :: γ) y ↔ e.IsValid m ∧ e.source = x ∧ IsBraidPath m e.target γ y :=
  Iff.rfl

theorem IsBraidPath.nil (x : List B) : IsBraidPath m x [] x := rfl

theorem IsBraidPath.singleton {e : BraidMove B} (he : e.IsValid m) :
    IsBraidPath m e.source [e] e.target :=
  ⟨he, rfl, rfl⟩

theorem IsBraidPath.append {x y z : List B} {γ δ : List (BraidMove B)}
    (hγ : IsBraidPath m x γ y) (hδ : IsBraidPath m y δ z) : IsBraidPath m x (γ ++ δ) z := by
  induction γ generalizing x with
  | nil => rw [hγ]; exact hδ
  | cons e γ ih => exact ⟨hγ.1, hγ.2.1, ih hγ.2.2⟩

theorem IsBraidPath.of_append {x z : List B} {γ δ : List (BraidMove B)}
    (h : IsBraidPath m x (γ ++ δ) z) : ∃ y, IsBraidPath m x γ y ∧ IsBraidPath m y δ z := by
  induction γ generalizing x with
  | nil => exact ⟨x, rfl, h⟩
  | cons e γ ih =>
    obtain ⟨y, h1, h2⟩ := ih h.2.2
    exact ⟨y, ⟨h.1, h.2.1, h1⟩, h2⟩

@[expose] def reversePath (γ : List (BraidMove B)) : List (BraidMove B) :=
  (γ.map BraidMove.reverse).reverse

@[simp] theorem reversePath_nil : reversePath ([] : List (BraidMove B)) = [] := rfl

@[simp] theorem reversePath_cons (e : BraidMove B) (γ : List (BraidMove B)) :
    reversePath (e :: γ) = reversePath γ ++ [e.reverse] := by
  simp [reversePath]

@[simp] theorem reversePath_append (γ δ : List (BraidMove B)) :
    reversePath (γ ++ δ) = reversePath δ ++ reversePath γ := by
  simp [reversePath]

@[simp] theorem reversePath_reversePath (γ : List (BraidMove B)) :
    reversePath (reversePath γ) = γ := by
  simp [reversePath, List.map_reverse, List.map_map, Function.comp_def]

theorem reversePath_map_extend (α β : List B) (γ : List (BraidMove B)) :
    reversePath (γ.map (BraidMove.extend α β)) = (reversePath γ).map (BraidMove.extend α β) := by
  simp [reversePath, List.map_reverse, List.map_map, Function.comp_def]

theorem IsBraidPath.reversePath (hm : ∀ a b, m a b = m b a) {x y : List B}
    {γ : List (BraidMove B)} (h : IsBraidPath m x γ y) :
    IsBraidPath m y (CFSG.Monster.B.Geometry.reversePath γ) x := by
  induction γ generalizing x with
  | nil => exact h.symm
  | cons e γ ih =>
    obtain ⟨he, rfl, hγ⟩ := h
    rw [reversePath_cons]
    exact (ih hγ).append ⟨he.reverse hm, rfl, rfl⟩

theorem IsBraidPath.extend {x y : List B} {γ : List (BraidMove B)} (h : IsBraidPath m x γ y)
    (α β : List B) :
    IsBraidPath m (α ++ x ++ β) (γ.map (BraidMove.extend α β)) (α ++ y ++ β) := by
  induction γ generalizing x with
  | nil => rw [h]; rfl
  | cons e γ ih =>
    obtain ⟨he, rfl, hγ⟩ := h
    exact ⟨he.extend α β, BraidMove.source_extend α β e,
      (BraidMove.target_extend α β e).symm ▸ ih hγ⟩

theorem IsBraidPath.cons {x y : List B} {γ : List (BraidMove B)} (h : IsBraidPath m x γ y)
    (a : B) : IsBraidPath m (a :: x) (γ.map (BraidMove.extend [a] [])) (a :: y) := by
  simpa using h.extend [a] []

theorem IsBraidPath.prepend {x y : List B} {γ : List (BraidMove B)} (h : IsBraidPath m x γ y)
    (α : List B) : IsBraidPath m (α ++ x) (γ.map (BraidMove.extend α [])) (α ++ y) := by
  simpa using h.extend α []

theorem IsBraidPath.postpend {x y : List B} {γ : List (BraidMove B)} (h : IsBraidPath m x γ y)
    (β : List B) : IsBraidPath m (x ++ β) (γ.map (BraidMove.extend [] β)) (y ++ β) := by
  simpa using h.extend [] β

theorem IsBraidPath.apply_eq {α : Type*} (f : List B → α)
    (hf : ∀ e : BraidMove B, e.IsValid m → f e.target = f e.source) {x y : List B}
    {γ : List (BraidMove B)} (h : IsBraidPath m x γ y) : f y = f x := by
  induction γ generalizing x with
  | nil => rw [h]
  | cons e γ ih =>
    obtain ⟨he, rfl, hγ⟩ := h
    rw [ih hγ, hf e he]

theorem IsBraidPath.isValid_of_mem {x y : List B} {γ : List (BraidMove B)}
    (h : IsBraidPath m x γ y) {e : BraidMove B} (he : e ∈ γ) : e.IsValid m := by
  induction γ generalizing x with
  | nil => simp at he
  | cons e' γ ih =>
    rcases List.mem_cons.1 he with rfl | he
    · exact h.1
    · exact ih h.2.2 he

theorem IsBraidPath.length_eq {x y : List B} {γ : List (BraidMove B)}
    (h : IsBraidPath m x γ y) : y.length = x.length :=
  h.apply_eq List.length fun e _ => e.length_target

theorem IsBraidPath.apply_source_eq {α : Type*} (f : List B → α)
    (hf : ∀ e : BraidMove B, e.IsValid m → f e.target = f e.source) {x y : List B}
    {γ : List (BraidMove B)} (h : IsBraidPath m x γ y) :
    ∀ e ∈ γ, f e.source = f x ∧ f e.target = f x := by
  induction γ generalizing x with
  | nil => simp
  | cons e γ ih =>
    obtain ⟨he, rfl, hγ⟩ := h
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact ⟨rfl, hf e' he⟩
    · obtain ⟨h1, h2⟩ := ih hγ e' he'
      exact ⟨h1.trans (hf e he), h2.trans (hf e he)⟩

inductive Elementary (m : B → B → ℕ) : List (BraidMove B) → List (BraidMove B) → Prop
  | backtrack (e : BraidMove B) : Elementary m [e, e.reverse] []
  | square (A C D : List B) (s t : B) (k : ℕ) (s' t' : B) (k' : ℕ) :
      Elementary m
        [⟨A, s, t, k, C ++ altWord s' t' k' ++ D⟩, ⟨A ++ altWord t s k ++ C, s', t', k', D⟩]
        [⟨A ++ altWord s t k ++ C, s', t', k', D⟩, ⟨A, s, t, k, C ++ altWord t' s' k' ++ D⟩]
  | loop (α β μ : List B) (c : List (BraidMove B)) (T : Finset B) (hT : T.card ≤ 3)
      (hc : IsBraidPath m μ c μ) (hcT : ∀ e ∈ c, ∀ b ∈ e.source, b ∈ T) :
      Elementary m (c.map (BraidMove.extend α β)) []

@[expose] def HomotopyStep (m : B → B → ℕ) (x y : List B) (γ γ' : List (BraidMove B)) : Prop :=
  IsBraidPath m x γ y ∧ IsBraidPath m x γ' y ∧
    ∃ p a b q, Elementary m a b ∧ γ = p ++ a ++ q ∧ γ' = p ++ b ++ q

@[expose] def Homotopic (m : B → B → ℕ) (x y : List B) :
    List (BraidMove B) → List (BraidMove B) → Prop :=
  Relation.EqvGen (HomotopyStep m x y)

namespace Homotopic

variable {x y : List B} {γ γ' γ'' : List (BraidMove B)}

@[refl] theorem refl (γ : List (BraidMove B)) : Homotopic m x y γ γ :=
  Relation.EqvGen.refl γ

@[symm] theorem symm (h : Homotopic m x y γ γ') : Homotopic m x y γ' γ :=
  Relation.EqvGen.symm _ _ h

@[trans] theorem trans (h : Homotopic m x y γ γ') (h' : Homotopic m x y γ' γ'') :
    Homotopic m x y γ γ'' :=
  Relation.EqvGen.trans _ _ _ h h'

theorem of_elementary {p a b q : List (BraidMove B)} (hab : Elementary m a b)
    (ha : IsBraidPath m x (p ++ a ++ q) y) (hb : IsBraidPath m x (p ++ b ++ q) y) :
    Homotopic m x y (p ++ a ++ q) (p ++ b ++ q) :=
  Relation.EqvGen.rel _ _ ⟨ha, hb, p, a, b, q, hab, rfl, rfl⟩

theorem context {u v : List B} (h : Homotopic m u v γ γ') {p q : List (BraidMove B)}
    (hp : IsBraidPath m x p u) (hq : IsBraidPath m v q y) :
    Homotopic m x y (p ++ γ ++ q) (p ++ γ' ++ q) := by
  induction h with
  | rel γ γ' h =>
    obtain ⟨h1, h2, p', a, b, q', hab, rfl, rfl⟩ := h
    refine Relation.EqvGen.rel _ _ ⟨(hp.append h1).append hq, (hp.append h2).append hq,
      p ++ p', a, b, q' ++ q, hab, ?_, ?_⟩ <;> simp
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem append_left {u : List B} (h : Homotopic m u y γ γ') {p : List (BraidMove B)}
    (hp : IsBraidPath m x p u) : Homotopic m x y (p ++ γ) (p ++ γ') := by
  simpa using h.context hp (IsBraidPath.nil y)

theorem append_right {v : List B} (h : Homotopic m x v γ γ') {q : List (BraidMove B)}
    (hq : IsBraidPath m v q y) : Homotopic m x y (γ ++ q) (γ' ++ q) := by
  simpa using h.context (IsBraidPath.nil x) hq

theorem isBraidPath_iff (h : Homotopic m x y γ γ') :
    IsBraidPath m x γ y ↔ IsBraidPath m x γ' y := by
  induction h with
  | rel γ γ' h => exact ⟨fun _ => h.2.1, fun _ => h.1⟩
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

theorem induction_on {P : List (BraidMove B) → List (BraidMove B) → Prop}
    (refl : ∀ γ, P γ γ) (symm : ∀ γ γ', P γ γ' → P γ' γ)
    (trans : ∀ γ γ' γ'', P γ γ' → P γ' γ'' → P γ γ'')
    (step : ∀ p a b q, Elementary m a b → IsBraidPath m x (p ++ a ++ q) y →
      IsBraidPath m x (p ++ b ++ q) y → P (p ++ a ++ q) (p ++ b ++ q))
    (h : Homotopic m x y γ γ') : P γ γ' := by
  induction h with
  | rel γ γ' h =>
    obtain ⟨h1, h2, p, a, b, q, hab, rfl, rfl⟩ := h
    exact step p a b q hab h1 h2
  | refl γ => exact refl γ
  | symm _ _ _ ih => exact symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact trans _ _ _ ih1 ih2

theorem apply_eq {α : Sort*} (f : List (BraidMove B) → α)
    (hf : ∀ p a b q, Elementary m a b → IsBraidPath m x (p ++ a ++ q) y →
      IsBraidPath m x (p ++ b ++ q) y → f (p ++ a ++ q) = f (p ++ b ++ q))
    (h : Homotopic m x y γ γ') : f γ = f γ' :=
  h.induction_on (P := fun γ γ' => f γ = f γ') (fun _ => rfl) (fun _ _ h => h.symm)
    (fun _ _ _ h h' => h.trans h') hf

end Homotopic

theorem Elementary.extend {a b : List (BraidMove B)} (h : Elementary m a b) (α β : List B) :
    Elementary m (a.map (BraidMove.extend α β)) (b.map (BraidMove.extend α β)) := by
  cases h with
  | backtrack e => exact .backtrack (e.extend α β)
  | square A C D s t k s' t' k' =>
    have h := Elementary.square (m := m) (α ++ A) C (D ++ β) s t k s' t' k'
    simp only [List.map_cons, List.map_nil, BraidMove.extend, List.append_assoc] at h ⊢
    exact h
  | loop α' β' μ c T hT hc hcT =>
    rw [List.map_map, BraidMove.extend_comp_extend, List.map_nil]
    exact .loop _ _ μ c T hT hc hcT

theorem Homotopic.extend {x y : List B} {γ γ' : List (BraidMove B)} (h : Homotopic m x y γ γ')
    (α β : List B) :
    Homotopic m (α ++ x ++ β) (α ++ y ++ β) (γ.map (BraidMove.extend α β))
      (γ'.map (BraidMove.extend α β)) := by
  induction h with
  | rel γ γ' h =>
    obtain ⟨h1, h2, p, a, b, q, hab, rfl, rfl⟩ := h
    refine Relation.EqvGen.rel _ _ ⟨h1.extend α β, h2.extend α β, p.map (BraidMove.extend α β),
      a.map (BraidMove.extend α β), b.map (BraidMove.extend α β), q.map (BraidMove.extend α β),
      hab.extend α β, ?_, ?_⟩ <;> simp
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem Homotopic.cons {x y : List B} {γ γ' : List (BraidMove B)} (h : Homotopic m x y γ γ')
    (a : B) :
    Homotopic m (a :: x) (a :: y) (γ.map (BraidMove.extend [a] []))
      (γ'.map (BraidMove.extend [a] [])) := by
  simpa using h.extend [a] []

theorem Homotopic.postpend {x y : List B} {γ γ' : List (BraidMove B)}
    (h : Homotopic m x y γ γ') (β : List B) :
    Homotopic m (x ++ β) (y ++ β) (γ.map (BraidMove.extend [] β))
      (γ'.map (BraidMove.extend [] β)) := by
  simpa using h.extend [] β

section Groupoid

variable (hm : ∀ a b, m a b = m b a)
include hm

theorem homotopic_append_reversePath {x y : List B} {γ : List (BraidMove B)}
    (h : IsBraidPath m x γ y) : Homotopic m x x (γ ++ reversePath γ) [] := by
  induction γ generalizing x with
  | nil =>
    rw [isBraidPath_nil] at h
    subst h
    exact Homotopic.refl _
  | cons e γ ih =>
    obtain ⟨he, rfl, hγ⟩ := h
    have h1 := (ih hγ).context (IsBraidPath.singleton he)
      (IsBraidPath.singleton (he.reverse hm))
    have h2 : Homotopic m e.source e.source ([] ++ [e, e.reverse] ++ []) ([] ++ [] ++ []) :=
      Homotopic.of_elementary (.backtrack e) ⟨he, rfl, he.reverse hm, rfl, rfl⟩ rfl
    simp only [List.nil_append, List.append_nil, List.singleton_append] at h1 h2
    rw [reversePath_cons, List.cons_append, ← List.append_assoc]
    exact h1.trans h2

theorem homotopic_reversePath_append {x y : List B} {γ : List (BraidMove B)}
    (h : IsBraidPath m x γ y) : Homotopic m y y (reversePath γ ++ γ) [] := by
  simpa using homotopic_append_reversePath hm (h.reversePath hm)

theorem Homotopic.reversePath {x y : List B} {γ γ' : List (BraidMove B)}
    (h : Homotopic m x y γ γ') (hγ : IsBraidPath m x γ y) :
    Homotopic m y x (CFSG.Monster.B.Geometry.reversePath γ)
      (CFSG.Monster.B.Geometry.reversePath γ') := by
  have hγ' := h.isBraidPath_iff.1 hγ
  have hr := hγ.reversePath hm
  have hr' := hγ'.reversePath hm
  have h1 := ((homotopic_append_reversePath hm hγ').append_left hr).symm
  have h2 := h.symm.context hr hr'
  have h3 := (homotopic_reversePath_append hm hγ).append_right hr'
  rw [List.append_nil, ← List.append_assoc] at h1
  rw [List.nil_append] at h3
  exact h1.trans (h2.trans h3)

theorem Homotopic.cancel_right {x y z : List B} {γ γ' δ : List (BraidMove B)}
    (h : Homotopic m x z (γ ++ δ) (γ' ++ δ)) (hγ : IsBraidPath m x γ y)
    (hγ' : IsBraidPath m x γ' y) (hδ : IsBraidPath m y δ z) : Homotopic m x y γ γ' := by
  have hr := hδ.reversePath hm
  have h1 := ((homotopic_append_reversePath hm hδ).context hγ (IsBraidPath.nil y)).symm
  have h2 := (homotopic_append_reversePath hm hδ).context hγ' (IsBraidPath.nil y)
  have h3 := h.append_right hr
  simp only [List.append_nil, ← List.append_assoc] at h1 h2
  exact h1.trans (h3.trans h2)

theorem Homotopic.cancel_left {u x y : List B} {p γ γ' : List (BraidMove B)}
    (h : Homotopic m u y (p ++ γ) (p ++ γ')) (hp : IsBraidPath m u p x)
    (hγ : IsBraidPath m x γ y) (hγ' : IsBraidPath m x γ' y) : Homotopic m x y γ γ' := by
  have h1 := ((homotopic_reversePath_append hm hp).append_right hγ).symm
  have h2 := (homotopic_reversePath_append hm hp).append_right hγ'
  have h3 := h.append_left (hp.reversePath hm)
  simp only [List.nil_append, List.append_assoc] at h1 h2 h3
  exact h1.trans (h3.trans h2)

theorem homotopic_of_append_reversePath {x y z : List B} {P Q R : List (BraidMove B)}
    (hP : IsBraidPath m x P z) (hQ : IsBraidPath m y Q z)
    (h : Homotopic m x y (P ++ reversePath Q) R) : Homotopic m x z P (R ++ Q) := by
  have h1 := ((homotopic_reversePath_append hm hQ).context hP (IsBraidPath.nil z)).symm
  have h2 := h.append_right hQ
  simp only [List.append_nil, ← List.append_assoc] at h1
  exact h1.trans h2

theorem homotopic_append_reversePath_of {a b c c' : List B} {P Q P' Q' X : List (BraidMove B)}
    (hP : IsBraidPath m a P c) (hQ : IsBraidPath m b Q c) (hX : IsBraidPath m c X c')
    (h1 : Homotopic m a c' (P ++ X) P') (h2 : Homotopic m b c' (Q ++ X) Q') :
    Homotopic m a b (P ++ reversePath Q) (P' ++ reversePath Q') := by
  have hQX := hQ.append hX
  have t1 := ((homotopic_append_reversePath hm hX).context hP (hQ.reversePath hm)).symm
  have t2 := h1.append_right (hQX.reversePath hm)
  have t3 := (h2.reversePath hm hQX).append_left (h1.isBraidPath_iff.1 (hP.append hX))
  simp only [List.append_nil, reversePath_append, ← List.append_assoc] at t1 t2 t3
  exact t1.trans (t2.trans t3)

theorem homotopic_of_forall_closed {x y : List B}
    (hx : ∀ γ, IsBraidPath m x γ x → Homotopic m x x γ []) {γ γ' : List (BraidMove B)}
    (hγ : IsBraidPath m x γ y) (hγ' : IsBraidPath m x γ' y) : Homotopic m x y γ γ' := by
  have h1 := ((homotopic_reversePath_append hm hγ').context hγ (IsBraidPath.nil y)).symm
  have h2 := (hx _ (hγ.append (hγ'.reversePath hm))).append_right hγ'
  simp only [List.append_nil, List.nil_append, ← List.append_assoc] at h1 h2
  exact h1.trans h2

end Groupoid

theorem Homotopic.of_elementary' {x y : List B} {a b : List (BraidMove B)}
    (hab : Elementary m a b) (ha : IsBraidPath m x a y) (hb : IsBraidPath m x b y) :
    Homotopic m x y a b := by
  simpa using Homotopic.of_elementary (p := []) (q := []) hab (by simpa using ha)
    (by simpa using hb)

theorem Elementary.square_extend (A : List B) (s t : B) (k : ℕ) (d : BraidMove B) :
    Elementary m [⟨A, s, t, k, d.source⟩, d.extend (A ++ altWord t s k) []]
      [d.extend (A ++ altWord s t k) [], ⟨A, s, t, k, d.target⟩] := by
  have h := Elementary.square (m := m) A d.pre d.suf s t k d.s d.t d.len
  simpa [BraidMove.extend, BraidMove.source, BraidMove.target] using h

theorem homotopic_slide {s t : B} {K : ℕ} {η₁ η₂ : List B} {δ : List (BraidMove B)}
    (he : (⟨[], s, t, K, η₁⟩ : BraidMove B).IsValid m) (hδ : IsBraidPath m η₁ δ η₂) :
    Homotopic m (altWord s t K ++ η₁) (altWord t s K ++ η₂)
      ((⟨[], s, t, K, η₁⟩ : BraidMove B) :: δ.map (BraidMove.extend (altWord t s K) []))
      (δ.map (BraidMove.extend (altWord s t K) []) ++ [⟨[], s, t, K, η₂⟩]) := by
  induction δ generalizing η₁ with
  | nil =>
    rw [isBraidPath_nil] at hδ
    subst hδ
    exact Homotopic.refl _
  | cons d δ ih =>
    obtain ⟨hd, rfl, hδ'⟩ := hδ
    have he' : (⟨[], s, t, K, d.target⟩ : BraidMove B).IsValid m := he
    have hsq := Elementary.square_extend (m := m) [] s t K d
    simp only [List.nil_append] at hsq
    have h1 : Homotopic m (altWord s t K ++ d.source) (altWord t s K ++ d.target)
        [⟨[], s, t, K, d.source⟩, d.extend (altWord t s K) []]
        [d.extend (altWord s t K) [], ⟨[], s, t, K, d.target⟩] := by
      refine Homotopic.of_elementary' hsq ⟨he, by simp [BraidMove.source], hd.extend _ _, ?_, ?_⟩
        ⟨hd.extend _ _, ?_, he', ?_, ?_⟩ <;>
        simp [BraidMove.source, BraidMove.target, BraidMove.extend]
    have h2 := h1.append_right (hδ'.prepend (altWord t s K))
    have hp : IsBraidPath m (altWord s t K ++ d.source) [d.extend (altWord s t K) []]
        (altWord s t K ++ d.target) := by
      simpa using (IsBraidPath.singleton hd).prepend (altWord s t K)
    have h3 := (ih he' hδ').append_left hp
    simp only [List.map_cons, List.cons_append, List.nil_append] at h2 h3 ⊢
    exact h2.trans h3

theorem IsBraidPath.mem_of_mem
    (hmove : ∀ e : BraidMove B, e.IsValid m → ∀ b ∈ e.target, b ∈ e.source)
    {x y : List B} {γ : List (BraidMove B)} (h : IsBraidPath m x γ y) :
    (∀ b ∈ y, b ∈ x) ∧ ∀ e ∈ γ, ∀ b ∈ e.source, b ∈ x := by
  induction γ generalizing x with
  | nil =>
    rw [isBraidPath_nil] at h
    subst h
    simp
  | cons e γ ih =>
    obtain ⟨he, rfl, hγ⟩ := h
    obtain ⟨h1, h2⟩ := ih hγ
    refine ⟨fun b hb => hmove e he b (h1 b hb), fun e' he' b hb => ?_⟩
    rcases List.mem_cons.1 he' with rfl | he'
    · exact hb
    · exact hmove e he b (h2 e' he' b hb)

theorem mem_altWord {a c b : B} {k : ℕ} (h : b ∈ altWord a c k) : b = a ∨ b = c := by
  induction k generalizing a c with
  | zero => simp at h
  | succ k ih =>
    rw [altWord_succ, List.mem_cons] at h
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact (ih h).symm

theorem mem_altWord_of_two_le (a c : B) {k : ℕ} (hk : 2 ≤ k) :
    a ∈ altWord a c k ∧ c ∈ altWord a c k := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  simp

theorem altWord_eq_cons_tail (a c : B) {k : ℕ} (hk : k ≠ 0) :
    altWord a c k = a :: (altWord a c k).tail := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rfl

theorem altWord_append_eq_cons (a c : B) {k : ℕ} (hk : k ≠ 0) (ζ : List B) :
    altWord a c k ++ ζ = a :: ((altWord a c k).tail ++ ζ) := by
  rw [← List.cons_append, ← altWord_eq_cons_tail a c hk]

theorem IsBraidPath.singleton_head {a c : B} {k : ℕ} {ζ : List B}
    (he : (⟨[], a, c, k, ζ⟩ : BraidMove B).IsValid m) :
    IsBraidPath m (a :: ((altWord a c k).tail ++ ζ)) [⟨[], a, c, k, ζ⟩]
      (c :: ((altWord c a k).tail ++ ζ)) := by
  rw [← altWord_append_eq_cons a c he.2.2, ← altWord_append_eq_cons c a he.2.2]
  exact IsBraidPath.singleton he

section Group

variable {W : Type*} [Group W] {S : Set W}

@[expose] noncomputable def pairOrder (S : Set W) (s t : S) : ℕ := orderOf ((s : W) * t)

@[expose] def leftDescents (S : Set W) (w : W) : Set S :=
  {s | wordLength S ((s : W) * w) < wordLength S w}

@[expose] def reducedWords (S : Set W) (w : W) : Set (List S) :=
  {l | IsReduced S l ∧ wordProd S l = w}

@[expose] def PairPrefix (S : Set W) : Prop :=
  ∀ (w : W) (s t : S), s ≠ t → s ∈ leftDescents S w → t ∈ leftDescents S w →
    IsReduced S (altWord s t (pairOrder S s t)) ∧
      wordLength S ((wordProd S (altWord s t (pairOrder S s t)))⁻¹ * w) =
        wordLength S w - pairOrder S s t

@[expose] def TriplePrefix (S : Set W) : Prop :=
  ∀ (w : W) (J : Finset S), J.card = 3 → (∀ s ∈ J, s ∈ leftDescents S w) →
    ∃ ρ : List S, IsReduced S ρ ∧ (∀ s ∈ ρ, s ∈ J) ∧
      (∀ s ∈ J, s ∈ leftDescents S (wordProd S ρ)) ∧
        wordLength S ((wordProd S ρ)⁻¹ * w) = wordLength S w - wordLength S (wordProd S ρ)

section Involutions

variable (hS2 : ∀ s ∈ S, orderOf s = 2)
include hS2

theorem pairOrder_comm (s t : S) : pairOrder S s t = pairOrder S t s := by
  unfold pairOrder
  rw [← orderOf_inv, mul_inv_rev, inv_eq_of_mul_eq_one_right (coe_mul_self_eq_one hS2 t),
    inv_eq_of_mul_eq_one_right (coe_mul_self_eq_one hS2 s)]

theorem pairOrder_ne_one {s t : S} (hst : s ≠ t) : pairOrder S s t ≠ 1 := by
  intro h
  rw [pairOrder, orderOf_eq_one_iff] at h
  exact hst (Subtype.ext ((eq_inv_of_mul_eq_one_left h).trans
    (inv_eq_of_mul_eq_one_right (coe_mul_self_eq_one hS2 t))))

theorem BraidMove.wordProd_target {e : BraidMove S} (he : e.IsValid (pairOrder S)) :
    wordProd S e.target = wordProd S e.source := by
  simp only [BraidMove.target, BraidMove.source, wordProd_append, wordProd_altWord]
  rw [(altProd_eq_altProd_iff (coe_mul_self_eq_one hS2 e.s) (coe_mul_self_eq_one hS2 e.t)).2
    (he.2.1 ▸ pow_orderOf_eq_one _)]

theorem BraidMove.mem_source_of_mem_target {e : BraidMove S} (he : e.IsValid (pairOrder S))
    {b : S} (hb : b ∈ e.target) : b ∈ e.source := by
  have h2 : 2 ≤ e.len := by
    have := pairOrder_ne_one hS2 he.1
    have := he.2.2
    rw [← he.2.1] at *
    omega
  simp only [BraidMove.target, BraidMove.source, List.mem_append] at hb ⊢
  rcases hb with (hb | hb) | hb
  · exact Or.inl (Or.inl hb)
  · rcases mem_altWord hb with rfl | rfl
    · exact Or.inl (Or.inr (mem_altWord_of_two_le _ _ h2).2)
    · exact Or.inl (Or.inr (mem_altWord_of_two_le _ _ h2).1)
  · exact Or.inr hb

theorem IsBraidPath.wordProd_eq {x y : List S} {γ : List (BraidMove S)}
    (h : IsBraidPath (pairOrder S) x γ y) : wordProd S y = wordProd S x :=
  h.apply_eq (wordProd S) fun _ he => BraidMove.wordProd_target hS2 he

theorem IsBraidPath.isReduced {x y : List S} {γ : List (BraidMove S)}
    (h : IsBraidPath (pairOrder S) x γ y) (hx : IsReduced S x) : IsReduced S y :=
  hx.of_length_eq (h.wordProd_eq hS2) h.length_eq

theorem IsBraidPath.isReduced_source {x y : List S} {γ : List (BraidMove S)}
    (h : IsBraidPath (pairOrder S) x γ y) (hx : IsReduced S x) :
    ∀ e ∈ γ, IsReduced S e.source ∧ wordProd S e.source = wordProd S x := by
  intro e he
  have h' := h.apply_source_eq (fun l => (wordProd S l, l.length))
    (fun e he => Prod.ext (BraidMove.wordProd_target hS2 he) e.length_target) e he
  simp only [Prod.mk.injEq] at h'
  exact ⟨hx.of_length_eq h'.1.1 h'.1.2, h'.1.1⟩

omit hS2 in
theorem isReduced_tail {s : S} {u v : List S} (hu : IsReduced S (s :: u))
    (hv : IsReduced S (s :: v)) (h : wordProd S (s :: u) = wordProd S (s :: v)) :
    IsReduced S u ∧ IsReduced S v ∧ wordProd S u = wordProd S v := by
  rw [wordProd_cons, wordProd_cons, mul_right_inj] at h
  exact ⟨hu.of_cons, hv.of_cons, h⟩

variable (hex : ExchangeCondition S)
include hex

theorem exists_isBraidPath {x y : List S} (hx : IsReduced S x) (hy : IsReduced S y)
    (hxy : wordProd S x = wordProd S y) : ∃ γ, IsBraidPath (pairOrder S) x γ y := by
  obtain ⟨n, hn⟩ : ∃ n, x.length = n := ⟨_, rfl⟩
  induction n generalizing x y with
  | zero =>
    obtain rfl := List.length_eq_zero_iff.1 hn
    obtain rfl := List.length_eq_zero_iff.1 ((hx.length_eq_length hy hxy).symm.trans hn)
    exact ⟨[], rfl⟩
  | succ n ih =>
    have head : ∀ (a : S) (u v : List S), u.length = n → IsReduced S (a :: u) →
        IsReduced S (a :: v) → wordProd S (a :: u) = wordProd S (a :: v) →
          ∃ γ, IsBraidPath (pairOrder S) (a :: u) γ (a :: v) := by
      intro a u v hu hau hav huv
      obtain ⟨hu', hv', huv'⟩ := isReduced_tail hau hav huv
      obtain ⟨γ, hγ⟩ := ih hu' hv' huv' hu
      exact ⟨_, hγ.cons a⟩
    obtain ⟨s, u, rfl⟩ := List.exists_cons_of_length_eq_add_one hn
    obtain ⟨t, v, rfl⟩ :=
      List.exists_cons_of_length_eq_add_one ((hx.length_eq_length hy hxy).symm.trans hn)
    have hu : u.length = n := by simpa using hn
    by_cases hst : s = t
    · subst hst
      exact head s u v hu hx hy hxy
    have hdt := hy.wordLength_mul_lt hS2
    rw [← hxy] at hdt
    obtain ⟨hm, σ, hA, hAp⟩ :=
      exists_isReduced_altWord_append hS2 hex hx (hx.wordLength_mul_lt hS2) hdt
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm
    have he : (⟨[], s, t, k + 1, σ⟩ : BraidMove S).IsValid (pairOrder S) :=
      ⟨hst, hk.symm, k.succ_ne_zero⟩
    rw [hk] at hA hAp
    have hBp := BraidMove.wordProd_target hS2 he
    have hB : IsReduced S (altWord t s (k + 1) ++ σ) := hA.of_length_eq hBp (by simp)
    obtain ⟨γ₁, hγ₁⟩ := head s u (altWord t s k ++ σ) hu hx hA hAp.symm
    have hlenA : (altWord s t (k + 1) ++ σ).length = n + 1 :=
      (hx.length_eq_length hA hAp.symm).symm.trans hn
    have hlen2 : (altWord s t k ++ σ).length = n := by
      simp only [List.length_append, length_altWord] at hlenA ⊢
      omega
    obtain ⟨γ₂, hγ₂⟩ := head t (altWord s t k ++ σ) v hlen2 hB hy (hBp.trans (hAp.trans hxy))
    exact ⟨γ₁ ++ [⟨[], s, t, k + 1, σ⟩] ++ γ₂, (hγ₁.append (IsBraidPath.singleton he)).append hγ₂⟩

omit hex in
private def AllHomotopic (n : ℕ) : Prop :=
  ∀ x y : List S, IsReduced S x → x.length = n → ∀ γ γ' : List (BraidMove S),
    IsBraidPath (pairOrder S) x γ y → IsBraidPath (pairOrder S) x γ' y →
      Homotopic (pairOrder S) x y γ γ'

private theorem homotopic_bracket {n : ℕ} (hIH : AllHomotopic (S := S) n) {s t : S} {K : ℕ}
    {η₁ η₂ : List S} (he : (⟨[], s, t, K, η₁⟩ : BraidMove S).IsValid (pairOrder S))
    (h₁ : IsReduced S (altWord s t K ++ η₁)) (h₂ : IsReduced S (altWord s t K ++ η₂))
    (hp : wordProd S (altWord s t K ++ η₁) = wordProd S (altWord s t K ++ η₂))
    (hlen : (altWord s t K ++ η₁).length = n + 1) {bs bt : List S}
    {π₁ π₂ π₁' π₂' : List (BraidMove S)}
    (hπ₁ : IsBraidPath (pairOrder S) bs π₁ ((altWord s t K).tail ++ η₁))
    (hπ₂ : IsBraidPath (pairOrder S) bs π₂ ((altWord s t K).tail ++ η₂))
    (hπ₁' : IsBraidPath (pairOrder S) bt π₁' ((altWord t s K).tail ++ η₁))
    (hπ₂' : IsBraidPath (pairOrder S) bt π₂' ((altWord t s K).tail ++ η₂)) :
    Homotopic (pairOrder S) (s :: bs) (t :: bt)
      (π₁.map (BraidMove.extend [s] []) ++ [⟨[], s, t, K, η₁⟩] ++
        reversePath (π₁'.map (BraidMove.extend [t] [])))
      (π₂.map (BraidMove.extend [s] []) ++ [⟨[], s, t, K, η₂⟩] ++
        reversePath (π₂'.map (BraidMove.extend [t] []))) := by
  have hm := pairOrder_comm hS2
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.2.2
  have he₂ : (⟨[], s, t, k + 1, η₂⟩ : BraidMove S).IsValid (pairOrder S) := he
  have hpη : wordProd S η₁ = wordProd S η₂ := by
    simpa only [wordProd_append, mul_right_inj] using hp
  obtain ⟨δ, hδ⟩ := exists_isBraidPath hS2 hex h₁.of_append_right h₂.of_append_right hpη
  have hB₁ : IsReduced S (altWord t s (k + 1) ++ η₁) :=
    h₁.of_length_eq (BraidMove.wordProd_target hS2 he) (by simp)
  have hu : IsReduced S (altWord t s k ++ η₁) := IsReduced.of_cons (s := s) h₁
  have hv : IsReduced S (altWord s t k ++ η₁) := IsReduced.of_cons (s := t) hB₁
  have hulen : (altWord t s k ++ η₁).length = n := by
    simp only [List.length_append, length_altWord] at hlen ⊢
    omega
  have hvlen : (altWord s t k ++ η₁).length = n := by
    simp only [List.length_append, length_altWord] at hlen ⊢
    omega
  have hbs : IsReduced S bs := (hπ₁.reversePath hm).isReduced hS2 hu
  have hbt : IsReduced S bt := (hπ₁'.reversePath hm).isReduced hS2 hv
  have hbslen : bs.length = n := hπ₁.length_eq.symm.trans hulen
  have hbtlen : bt.length = n := hπ₁'.length_eq.symm.trans hvlen
  have hDs := hδ.prepend (altWord t s k)
  have hDt := hδ.prepend (altWord s t k)
  have hXs : δ.map (BraidMove.extend (altWord s t (k + 1)) []) =
      (δ.map (BraidMove.extend (altWord t s k) [])).map (BraidMove.extend [s] []) := by
    rw [List.map_map, BraidMove.extend_comp_extend]
    rfl
  have hXt : δ.map (BraidMove.extend (altWord t s (k + 1)) []) =
      (δ.map (BraidMove.extend (altWord s t k) [])).map (BraidMove.extend [t] []) := by
    rw [List.map_map, BraidMove.extend_comp_extend]
    rfl
  have hsl := homotopic_slide he hδ
  rw [hXs, hXt] at hsl
  have hP₁ := hπ₁.cons s
  have hQ₁ := hπ₁'.cons t
  have hLA := (hIH bs _ hbs hbslen _ _ (hπ₁.append hDs) hπ₂).cons s
  have hLB := (hIH bt _ hbt hbtlen _ _ (hπ₁'.append hDt) hπ₂').cons t
  rw [List.map_append] at hLA hLB
  have h1 : Homotopic (pairOrder S) (s :: bs) (t :: (altWord s t k ++ η₂))
      (π₁.map (BraidMove.extend [s] []) ++ [⟨[], s, t, k + 1, η₁⟩] ++
        (δ.map (BraidMove.extend (altWord s t k) [])).map (BraidMove.extend [t] []))
      (π₂.map (BraidMove.extend [s] []) ++ [⟨[], s, t, k + 1, η₂⟩]) := by
    have t1 := hsl.append_left hP₁
    have t2 := hLA.append_right (IsBraidPath.singleton he₂)
    simp only [List.append_assoc, List.singleton_append] at t1 t2 ⊢
    exact t1.trans t2
  exact homotopic_append_reversePath_of hm (hP₁.append (IsBraidPath.singleton he)) hQ₁
    (hDt.cons t) h1 hLB

end Involutions

private structure StepData (S : Set W) (w : W) where
  bt : S → List S
  pi : S → List S → List (BraidMove S)
  ref : S → S → List S
  hbt : ∀ s u, s :: u ∈ reducedWords S w → s :: bt s ∈ reducedWords S w
  hpi : ∀ s u, s :: u ∈ reducedWords S w → IsBraidPath (pairOrder S) (bt s) (pi s u) u
  href : ∀ s t u v, s ≠ t → s :: u ∈ reducedWords S w → t :: v ∈ reducedWords S w →
    altWord s t (pairOrder S s t) ++ ref s t ∈ reducedWords S w ∧ pairOrder S s t ≠ 0

variable {w : W}

private def StepData.path (D : StepData S w) (s : S) (u : List S) : List (BraidMove S) :=
  (D.pi s u).map (BraidMove.extend [s] [])

private noncomputable def StepData.bracket (D : StepData S w) (s t : S) : List (BraidMove S) :=
  D.path s ((altWord s t (pairOrder S s t)).tail ++ D.ref s t) ++
    [⟨[], s, t, pairOrder S s t, D.ref s t⟩] ++
      reversePath (D.path t ((altWord t s (pairOrder S s t)).tail ++ D.ref s t))

private noncomputable def StepData.stepBracket (D : StepData S w) (e : BraidMove S) :
    List (BraidMove S) :=
  match e.pre with
  | [] => D.bracket e.s e.t
  | _ :: _ => []

private noncomputable def StepData.walk (D : StepData S w) (γ : List (BraidMove S)) :
    List (BraidMove S) :=
  γ.flatMap D.stepBracket

private def StepData.pathW (D : StepData S w) : List S → List (BraidMove S)
  | [] => []
  | s :: u => D.path s u

private def StepData.base (D : StepData S w) : List S → List S
  | [] => []
  | s :: _ => s :: D.bt s

private theorem StepData.walk_append (D : StepData S w) (γ δ : List (BraidMove S)) :
    D.walk (γ ++ δ) = D.walk γ ++ D.walk δ :=
  List.flatMap_append

private theorem StepData.walk_map_extend (D : StepData S w) (a : S) (α β : List S)
    (γ : List (BraidMove S)) :
    D.walk (γ.map (BraidMove.extend (a :: α) β)) = [] := by
  induction γ with
  | nil => rfl
  | cons e γ ih =>
    simp only [List.map_cons, StepData.walk, List.flatMap_cons] at ih ⊢
    rw [ih]
    rfl

section Step

variable (hS2 : ∀ s ∈ S, orderOf s = 2) (hex : ExchangeCondition S)
include hS2 hex

private theorem StepData.nonempty (w : W) : Nonempty (StepData S w) := by
  have h1 : ∀ s : S, ∃ b : List S,
      (∃ u, s :: u ∈ reducedWords S w) → s :: b ∈ reducedWords S w := by
    intro s
    by_cases h : ∃ u, s :: u ∈ reducedWords S w
    · obtain ⟨u, hu⟩ := h
      exact ⟨u, fun _ => hu⟩
    · exact ⟨[], fun h' => absurd h' h⟩
  choose bt hbt using h1
  have h2 : ∀ (s : S) (u : List S), ∃ γ : List (BraidMove S),
      s :: u ∈ reducedWords S w → IsBraidPath (pairOrder S) (bt s) γ u := by
    intro s u
    by_cases h : s :: u ∈ reducedWords S w
    · have hb := hbt s ⟨u, h⟩
      obtain ⟨hb1, hb2, hb3⟩ := isReduced_tail hb.1 h.1 (hb.2.trans h.2.symm)
      obtain ⟨γ, hγ⟩ := exists_isBraidPath hS2 hex hb1 hb2 hb3
      exact ⟨γ, fun _ => hγ⟩
    · exact ⟨[], fun h' => absurd h' h⟩
  choose pi hpi using h2
  have h3 : ∀ s t : S, ∃ σ : List S, ∀ u v, s ≠ t → s :: u ∈ reducedWords S w →
      t :: v ∈ reducedWords S w →
        altWord s t (pairOrder S s t) ++ σ ∈ reducedWords S w ∧ pairOrder S s t ≠ 0 := by
    intro s t
    by_cases h : ∃ u v, s ≠ t ∧ s :: u ∈ reducedWords S w ∧ t :: v ∈ reducedWords S w
    · obtain ⟨u, v, -, hu, hv⟩ := h
      have hdt := hv.1.wordLength_mul_lt hS2
      rw [hv.2, ← hu.2] at hdt
      obtain ⟨hm, σ, hA, hAp⟩ :=
        exists_isReduced_altWord_append hS2 hex hu.1 (hu.1.wordLength_mul_lt hS2) hdt
      exact ⟨σ, fun _ _ _ _ _ => ⟨⟨hA, hAp.trans hu.2⟩, hm⟩⟩
    · exact ⟨[], fun u v hst hu hv => absurd ⟨u, v, hst, hu, hv⟩ h⟩
  choose ref href using h3
  exact ⟨⟨bt, pi, ref, fun s u h => hbt s ⟨u, h⟩, hpi, href⟩⟩

variable {w : W}

omit hS2 hex in
private theorem StepData.isBraidPath_path (D : StepData S w) {s : S} {u : List S}
    (h : s :: u ∈ reducedWords S w) :
    IsBraidPath (pairOrder S) (s :: D.bt s) (D.path s u) (s :: u) :=
  (D.hpi s u h).cons s

omit hS2 hex in
private theorem StepData.isBraidPath_pathW (D : StepData S w) {x : List S}
    (hx : x ∈ reducedWords S w) :
    IsBraidPath (pairOrder S) (D.base x) (D.pathW x) x := by
  cases x with
  | nil => rfl
  | cons s u => exact D.isBraidPath_path hx

omit hex in
private theorem mem_reducedWords_target {e : BraidMove S} (he : e.IsValid (pairOrder S))
    (h : e.source ∈ reducedWords S w) : e.target ∈ reducedWords S w :=
  ⟨h.1.of_length_eq (BraidMove.wordProd_target hS2 he) e.length_target,
    (BraidMove.wordProd_target hS2 he).trans h.2⟩

omit hex in
private theorem StepData.isBraidPath_bracket (D : StepData S w) {s t : S} {u v : List S}
    (hst : s ≠ t)
    (hs : s :: u ∈ reducedWords S w) (ht : t :: v ∈ reducedWords S w) :
    IsBraidPath (pairOrder S) (s :: D.bt s) (D.bracket s t) (t :: D.bt t) := by
  obtain ⟨hz, hK⟩ := D.href s t u v hst hs ht
  have he : (⟨[], s, t, pairOrder S s t, D.ref s t⟩ : BraidMove S).IsValid (pairOrder S) :=
    ⟨hst, rfl, hK⟩
  have hz' : s :: ((altWord s t (pairOrder S s t)).tail ++ D.ref s t) ∈ reducedWords S w := by
    rw [← List.cons_append, ← altWord_eq_cons_tail _ _ hK]
    exact hz
  have hz'' := mem_reducedWords_target hS2 he hz
  have hzt : altWord t s (pairOrder S s t) ++ D.ref s t =
      t :: ((altWord t s (pairOrder S s t)).tail ++ D.ref s t) := by
    rw [← List.cons_append, ← altWord_eq_cons_tail _ _ hK]
  have hz''' : t :: ((altWord t s (pairOrder S s t)).tail ++ D.ref s t) ∈ reducedWords S w := by
    rw [← hzt]
    exact hz''
  refine ((D.isBraidPath_path hz').append ?_).append
    ((D.isBraidPath_path hz''').reversePath (pairOrder_comm hS2))
  rw [← List.cons_append, ← altWord_eq_cons_tail _ _ hK, ← hzt]
  exact IsBraidPath.singleton he

private theorem StepData.homotopic_path_append_move (D : StepData S w) {n : ℕ}
    (hIH : AllHomotopic (S := S) n) {s t : S}
    {K : ℕ} {η : List S} (he : (⟨[], s, t, K, η⟩ : BraidMove S).IsValid (pairOrder S))
    (hx : altWord s t K ++ η ∈ reducedWords S w) (hlen : (altWord s t K ++ η).length = n + 1) :
    Homotopic (pairOrder S) (s :: D.bt s) (altWord t s K ++ η)
      (D.path s ((altWord s t K).tail ++ η) ++ [⟨[], s, t, K, η⟩])
      (D.bracket s t ++ D.path t ((altWord t s K).tail ++ η)) := by
  have hst : s ≠ t := he.1
  have hK1 : K = pairOrder S s t := he.2.1
  have hK : K ≠ 0 := he.2.2
  subst hK1
  have hcons : ∀ (a b : S) (ζ : List S), altWord a b (pairOrder S s t) ++ ζ =
      a :: ((altWord a b (pairOrder S s t)).tail ++ ζ) := fun a b ζ => by
    rw [← List.cons_append, ← altWord_eq_cons_tail _ _ hK]
  have hxs : s :: ((altWord s t (pairOrder S s t)).tail ++ η) ∈ reducedWords S w := by
    rw [← hcons]
    exact hx
  have hy := mem_reducedWords_target hS2 he hx
  have hyt : t :: ((altWord t s (pairOrder S s t)).tail ++ η) ∈ reducedWords S w := by
    rw [← hcons]
    exact hy
  obtain ⟨hz, -⟩ := D.href s t _ _ hst hxs hyt
  have hzs : s :: ((altWord s t (pairOrder S s t)).tail ++ D.ref s t) ∈ reducedWords S w := by
    rw [← hcons]
    exact hz
  have hz' := mem_reducedWords_target hS2 (⟨hst, rfl, hK⟩ :
    (⟨[], s, t, pairOrder S s t, D.ref s t⟩ : BraidMove S).IsValid (pairOrder S)) hz
  have hzt : t :: ((altWord t s (pairOrder S s t)).tail ++ D.ref s t) ∈ reducedWords S w := by
    rw [← hcons]
    exact hz'
  have hb := homotopic_bracket hS2 hex hIH he hx.1 hz.1 (hx.2.trans hz.2.symm) hlen
    (D.hpi s _ hxs) (D.hpi s _ hzs) (D.hpi t _ hyt) (D.hpi t _ hzt)
  have hP : IsBraidPath (pairOrder S) (s :: D.bt s)
      (D.path s ((altWord s t (pairOrder S s t)).tail ++ η) ++ [⟨[], s, t, pairOrder S s t, η⟩])
      (altWord t s (pairOrder S s t) ++ η) := by
    refine (D.isBraidPath_path hxs).append ?_
    rw [← hcons]
    exact IsBraidPath.singleton he
  have hQ : IsBraidPath (pairOrder S) (t :: D.bt t)
      (D.path t ((altWord t s (pairOrder S s t)).tail ++ η))
      (altWord t s (pairOrder S s t) ++ η) := by
    rw [hcons]
    exact D.isBraidPath_path hyt
  exact homotopic_of_append_reversePath (pairOrder_comm hS2) hP hQ hb

omit hS2 hex in
private theorem StepData.isReduced_bt (D : StepData S w) {n : ℕ} {s : S} {u : List S}
    (hs : s :: u ∈ reducedWords S w) (hlen : (s :: u).length = n + 1) :
    IsReduced S (D.bt s) ∧ (D.bt s).length = n := by
  have hb := D.hbt s u hs
  refine ⟨hb.1.of_cons, ?_⟩
  have := (hb.1.length_eq_length hs.1 (hb.2.trans hs.2.symm)).trans hlen
  simpa using this

private theorem StepData.homotopic_walk (D : StepData S w) {n : ℕ}
    (hIH : AllHomotopic (S := S) n) {x y : List S} {γ : List (BraidMove S)}
    (hx : x ∈ reducedWords S w) (hlen : x.length = n + 1)
    (hγ : IsBraidPath (pairOrder S) x γ y) :
    Homotopic (pairOrder S) (D.base x) y (D.pathW x ++ γ) (D.walk γ ++ D.pathW y) := by
  induction γ generalizing x with
  | nil =>
    rw [isBraidPath_nil] at hγ
    subst hγ
    simpa [StepData.walk] using Homotopic.refl (m := pairOrder S) (x := D.base x) (y := x)
      (D.pathW x)
  | cons e γ ih =>
    obtain ⟨he, rfl, hγ'⟩ := hγ
    have hy := mem_reducedWords_target hS2 he hx
    have hylen : e.target.length = n + 1 := e.length_target.trans hlen
    have h2 := ih hy hylen hγ'
    obtain ⟨pre, s, t, K, η⟩ := e
    cases pre with
    | nil =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.2.2
      have hst : s ≠ t := he.1
      have h1 := D.homotopic_path_append_move hS2 hex hIH he hx hlen
      have hxs : s :: (altWord t s k ++ η) ∈ reducedWords S w := hx
      have hyt : t :: (altWord s t k ++ η) ∈ reducedWords S w := hy
      have t1 := h1.append_right hγ'
      have t2 : Homotopic (pairOrder S) (s :: D.bt s) y
          (D.bracket s t ++ (D.path t (altWord s t k ++ η) ++ γ))
          (D.bracket s t ++ (D.walk γ ++ D.pathW y)) :=
        h2.append_left (D.isBraidPath_bracket hS2 hst hxs hyt)
      have t3 : Homotopic (pairOrder S) (s :: D.bt s) y
          (D.path s (altWord t s k ++ η) ++ [⟨[], s, t, k + 1, η⟩] ++ γ)
          (D.bracket s t ++ D.path t (altWord s t k ++ η) ++ γ) := t1
      rw [List.append_assoc] at t3
      rw [List.append_assoc (D.bracket s t)] at t3
      have t4 := t3.trans t2
      simp only [List.singleton_append] at t4
      change Homotopic (pairOrder S) (s :: D.bt s) y
        (D.path s (altWord t s k ++ η) ++ ⟨[], s, t, k + 1, η⟩ :: γ)
        ((D.bracket s t ++ D.walk γ) ++ D.pathW y)
      rw [List.append_assoc]
      exact t4
    | cons a pre' =>
      have hxa : a :: (pre' ++ altWord s t K ++ η) ∈ reducedWords S w := hx
      have e₀v : (⟨pre', s, t, K, η⟩ : BraidMove S).IsValid (pairOrder S) := he
      obtain ⟨hbt, hbtlen⟩ := D.isReduced_bt hxa hlen
      have hp₁ := (D.hpi a _ hxa).append (IsBraidPath.singleton e₀v)
      have hya : a :: (pre' ++ altWord t s K ++ η) ∈ reducedWords S w := hy
      have hp₂ := D.hpi a _ hya
      have hLA := (hIH _ _ hbt hbtlen _ _ hp₁ hp₂).cons a
      have hext : (⟨pre', s, t, K, η⟩ : BraidMove S).extend [a] [] = ⟨a :: pre', s, t, K, η⟩ := by
        simp [BraidMove.extend]
      rw [List.map_append, List.map_singleton, hext] at hLA
      have t1 : Homotopic (pairOrder S) (a :: D.bt a) y
          (D.path a (pre' ++ altWord s t K ++ η) ++ [⟨a :: pre', s, t, K, η⟩] ++ γ)
          (D.path a (pre' ++ altWord t s K ++ η) ++ γ) := hLA.append_right hγ'
      rw [List.append_assoc (D.path a (pre' ++ altWord s t K ++ η))] at t1
      have t2 : Homotopic (pairOrder S) (a :: D.bt a) y
          (D.path a (pre' ++ altWord t s K ++ η) ++ γ) (D.walk γ ++ D.pathW y) := h2
      exact t1.trans t2

private theorem StepData.homotopic_bracket_reverse (D : StepData S w) {n : ℕ}
    (hIH : AllHomotopic (S := S) n) {s t : S} {u v : List S} (hst : s ≠ t)
    (hs : s :: u ∈ reducedWords S w) (ht : t :: v ∈ reducedWords S w)
    (hlen : (s :: u).length = n + 1) :
    Homotopic (pairOrder S) (s :: D.bt s) (s :: D.bt s) (D.bracket s t ++ D.bracket t s) [] := by
  have hcomm := pairOrder_comm hS2 t s
  obtain ⟨hz, hK⟩ := D.href s t u v hst hs ht
  obtain ⟨hz₂, -⟩ := D.href t s v u hst.symm ht hs
  rw [hcomm] at hz₂
  have hf : (⟨[], t, s, pairOrder S s t, D.ref t s⟩ : BraidMove S).IsValid (pairOrder S) :=
    ⟨hst.symm, hcomm.symm, hK⟩
  have hz₃ := mem_reducedWords_target hS2 hf hz₂
  have hf' : (⟨[], s, t, pairOrder S s t, D.ref t s⟩ : BraidMove S).IsValid (pairOrder S) :=
    ⟨hst, rfl, hK⟩
  have hfr : (⟨[], s, t, pairOrder S s t, D.ref s t⟩ : BraidMove S).IsValid (pairOrder S) :=
    ⟨hst, rfl, hK⟩
  have hcons : ∀ (a b : S) (ζ : List S), altWord a b (pairOrder S s t) ++ ζ =
      a :: ((altWord a b (pairOrder S s t)).tail ++ ζ) := fun a b ζ => by
    rw [← List.cons_append, ← altWord_eq_cons_tail _ _ hK]
  have hmem : ∀ (a b : S) (ζ : List S), altWord a b (pairOrder S s t) ++ ζ ∈ reducedWords S w →
      a :: ((altWord a b (pairOrder S s t)).tail ++ ζ) ∈ reducedWords S w := fun a b ζ h => by
    rw [← hcons]
    exact h
  have hzlen : (altWord s t (pairOrder S s t) ++ D.ref t s).length = n + 1 :=
    (hz₃.1.length_eq_length hs.1 (hz₃.2.trans hs.2.symm)).trans hlen
  have hb := homotopic_bracket hS2 hex hIH hf' hz₃.1 hz.1 (hz₃.2.trans hz.2.symm) hzlen
    (D.hpi s _ (hmem s t _ hz₃)) (D.hpi s _ (hmem s t _ hz))
    (D.hpi t _ (hmem t s _ (mem_reducedWords_target hS2 hf' hz₃)))
    (D.hpi t _ (hmem t s _ (mem_reducedWords_target hS2 hfr hz)))
  have hrev : reversePath (D.bracket t s) =
      D.path s ((altWord s t (pairOrder S s t)).tail ++ D.ref t s) ++
        [⟨[], s, t, pairOrder S s t, D.ref t s⟩] ++
          reversePath (D.path t ((altWord t s (pairOrder S s t)).tail ++ D.ref t s)) := by
    simp only [StepData.bracket, hcomm, reversePath_append, reversePath_reversePath,
      reversePath_cons, reversePath_nil, List.nil_append, BraidMove.reverse, List.append_assoc]
  have hbr := D.isBraidPath_bracket hS2 hst.symm ht hs
  have h1 : Homotopic (pairOrder S) (s :: D.bt s) (s :: D.bt s)
      (D.bracket s t ++ D.bracket t s) (reversePath (D.bracket t s) ++ D.bracket t s) := by
    rw [hrev]
    exact hb.symm.append_right hbr
  exact h1.trans (homotopic_reversePath_append (pairOrder_comm hS2) hbr)

omit hS2 hex in
private theorem StepData.walk_map_map_extend (D : StepData S w) (p : S) (η : List S)
    (δ : List (BraidMove S)) :
    D.walk ((δ.map (BraidMove.extend [p] [])).map (BraidMove.extend [] η)) = [] := by
  rw [List.map_map, BraidMove.extend_comp_extend]
  exact D.walk_map_extend p [] ([] ++ η) δ

private theorem StepData.homotopic_bracket_triangle (D : StepData S w) (htriple : TriplePrefix S)
    {n : ℕ} (hIH : AllHomotopic (S := S) n) {a b c : S} {ua ub uc : List S}
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (ha : a :: ua ∈ reducedWords S w) (hb : b :: ub ∈ reducedWords S w)
    (hc : c :: uc ∈ reducedWords S w) (hlen : (a :: ua).length = n + 1) :
    Homotopic (pairOrder S) (a :: D.bt a) (c :: D.bt c)
      (D.bracket a b ++ D.bracket b c) (D.bracket a c) := by
  classical
  have hm := pairOrder_comm hS2
  have hdesc : ∀ {p : S} {u : List S}, p :: u ∈ reducedWords S w → p ∈ leftDescents S w := by
    intro p u hp
    have := hp.1.wordLength_mul_lt hS2
    rwa [hp.2] at this
  have hJcard : ({a, b, c} : Finset S).card = 3 :=
    Finset.card_eq_three.2 ⟨a, b, c, hab, hca.symm, hbc, rfl⟩
  have hJD : ∀ s ∈ ({a, b, c} : Finset S), s ∈ leftDescents S w := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact hdesc ha
    · exact hdesc hb
    · exact hdesc hc
  obtain ⟨ρ, hρ, hρJ, hJv, hℓ⟩ := htriple w {a, b, c} hJcard hJD
  obtain ⟨v, hv⟩ : ∃ v, wordProd S ρ = v := ⟨_, rfl⟩
  rw [hv] at hJv hℓ
  obtain ⟨η, hη, hηp⟩ := exists_isReduced_wordProd_eq (S := S) (ρ.reverse ++ (a :: ua))
  have hηp' : wordProd S η = v⁻¹ * w := by
    rw [hηp, wordProd_append, wordProd_reverse hS2, ha.2, hv]
  have hvw : wordLength S v ≤ wordLength S w := by
    by_contra hlt
    replace hlt := not_le.1 hlt
    have h0 : η.length = 0 := by
      rw [hη.length_eq, hηp', hℓ]
      omega
    rw [List.length_eq_zero_iff] at h0
    rw [h0, wordProd_nil] at hηp'
    rw [← inv_mul_eq_one.1 hηp'.symm] at hlt
    exact lt_irrefl _ hlt
  have happ : ∀ y : List S, y ∈ reducedWords S v → y ++ η ∈ reducedWords S w := by
    intro y hy
    have hprod : wordProd S (y ++ η) = w := by
      rw [wordProd_append, hy.2, hηp', mul_inv_cancel_left]
    refine ⟨?_, hprod⟩
    change (y ++ η).length = wordLength S (wordProd S (y ++ η))
    rw [hprod, List.length_append, hy.1.length_eq, hy.2, hη.length_eq, hηp', hℓ]
    omega
  have hvJ : ∀ y : List S, y ∈ reducedWords S v → ∀ p ∈ y, p ∈ ({a, b, c} : Finset S) := by
    intro y hy p hp
    obtain ⟨γ, hγ⟩ := exists_isBraidPath hS2 hex hρ hy.1 (hv.trans hy.2.symm)
    exact hρJ p ((hγ.mem_of_mem fun e he _ hb =>
      BraidMove.mem_source_of_mem_target hS2 he hb).1 p hp)
  have hpair : ∀ p q : S, p ∈ ({a, b, c} : Finset S) → q ∈ ({a, b, c} : Finset S) →
      ∃ ζ : List S, altWord p q (pairOrder S p q) ++ ζ ∈ reducedWords S v ∧
        pairOrder S p q ≠ 0 := by
    intro p q hp hq
    have hpv := hJv p hp
    have hqv := hJv q hq
    rw [← hv] at hpv hqv
    obtain ⟨hm0, ζ, hA, hAp⟩ := exists_isReduced_altWord_append hS2 hex hρ hpv hqv
    exact ⟨ζ, ⟨hA, hAp.trans hv⟩, hm0⟩
  have hhead : ∀ (p : S) (u u' : List S), p :: u ∈ reducedWords S v →
      p :: u' ∈ reducedWords S v → ∃ δ, IsBraidPath (pairOrder S) u δ u' := by
    intro p u u' hu hu'
    obtain ⟨h1, h2, h3⟩ := isReduced_tail hu.1 hu'.1 (hu.2.trans hu'.2.symm)
    exact exists_isBraidPath hS2 hex h1 h2 h3
  have hmemA : a ∈ ({a, b, c} : Finset S) := by simp
  have hmemB : b ∈ ({a, b, c} : Finset S) := by simp
  have hmemC : c ∈ ({a, b, c} : Finset S) := by simp
  obtain ⟨ζab, hzab, hKab⟩ := hpair a b hmemA hmemB
  obtain ⟨ζbc, hzbc, hKbc⟩ := hpair b c hmemB hmemC
  obtain ⟨ζca, hzca, hKca⟩ := hpair c a hmemC hmemA
  have hfab : (⟨[], a, b, pairOrder S a b, ζab⟩ : BraidMove S).IsValid (pairOrder S) :=
    ⟨hab, rfl, hKab⟩
  have hfbc : (⟨[], b, c, pairOrder S b c, ζbc⟩ : BraidMove S).IsValid (pairOrder S) :=
    ⟨hbc, rfl, hKbc⟩
  have hfca : (⟨[], c, a, pairOrder S c a, ζca⟩ : BraidMove S).IsValid (pairOrder S) :=
    ⟨hca, rfl, hKca⟩
  have hvmem : ∀ {e : BraidMove S}, e.IsValid (pairOrder S) → e.source ∈ reducedWords S v →
      e.target ∈ reducedWords S v := fun he h => mem_reducedWords_target hS2 he h
  have hsab : altWord b a (pairOrder S a b) ++ ζab ∈ reducedWords S v := hvmem hfab hzab
  have hsbc : altWord c b (pairOrder S b c) ++ ζbc ∈ reducedWords S v := hvmem hfbc hzbc
  have hsca : altWord a c (pairOrder S c a) ++ ζca ∈ reducedWords S v := hvmem hfca hzca
  rw [altWord_append_eq_cons a b hKab] at hzab
  rw [altWord_append_eq_cons b a hKab] at hsab
  rw [altWord_append_eq_cons b c hKbc] at hzbc
  rw [altWord_append_eq_cons c b hKbc] at hsbc
  rw [altWord_append_eq_cons c a hKca] at hzca
  rw [altWord_append_eq_cons a c hKca] at hsca
  obtain ⟨δb, hδb⟩ := hhead b _ _ hsab hzbc
  obtain ⟨δc, hδc⟩ := hhead c _ _ hsbc hzca
  obtain ⟨δa, hδa⟩ := hhead a _ _ hsca hzab
  set L : List (BraidMove S) := [⟨[], a, b, pairOrder S a b, ζab⟩] ++
    δb.map (BraidMove.extend [b] []) ++ [⟨[], b, c, pairOrder S b c, ζbc⟩] ++
      δc.map (BraidMove.extend [c] []) ++ [⟨[], c, a, pairOrder S c a, ζca⟩] ++
        δa.map (BraidMove.extend [a] []) with hL
  have hLp : IsBraidPath (pairOrder S) _ L _ :=
    (((((IsBraidPath.singleton_head hfab).append (hδb.cons b)).append
      (IsBraidPath.singleton_head hfbc)).append (hδc.cons c)).append
        (IsBraidPath.singleton_head hfca)).append (hδa.cons a)
  have hLJ : ∀ e ∈ L, ∀ p ∈ e.source, p ∈ ({a, b, c} : Finset S) := by
    intro e he p hp
    obtain ⟨h1, h2⟩ := hLp.isReduced_source hS2 hzab.1 e he
    exact hvJ _ ⟨h1, h2.trans hzab.2⟩ p hp
  have hLη := hLp.postpend η
  have hloop := Homotopic.of_elementary'
    (Elementary.loop [] η _ L {a, b, c} hJcard.le hLp hLJ) hLη (IsBraidPath.nil _)
  have hxw := happ _ hzab
  have hxlen : (a :: ((altWord a b (pairOrder S a b)).tail ++ ζab) ++ η).length = n + 1 :=
    (hxw.1.length_eq_length ha.1 (hxw.2.trans ha.2.symm)).trans hlen
  have hwalk := D.homotopic_walk hS2 hex hIH hxw hxlen hLη
  have hWL : D.walk (L.map (BraidMove.extend [] η)) =
      D.bracket a b ++ D.bracket b c ++ D.bracket c a := by
    simp only [hL, List.map_append, StepData.walk_append, D.walk_map_map_extend]
    simp [StepData.walk, StepData.stepBracket, BraidMove.extend]
  rw [hWL] at hwalk
  have hpx := D.isBraidPath_pathW hxw
  have h1 := (hloop.append_left hpx).symm.trans hwalk
  rw [List.append_nil] at h1
  have hbab := D.isBraidPath_bracket hS2 hab ha hb
  have hbbc := D.isBraidPath_bracket hS2 hbc hb hc
  have hbca := D.isBraidPath_bracket hS2 hca hc ha
  have hbac := D.isBraidPath_bracket hS2 hca.symm ha hc
  have h1' : Homotopic (pairOrder S) (a :: D.bt a)
      (a :: ((altWord a b (pairOrder S a b)).tail ++ ζab) ++ η)
      ([] ++ D.pathW (a :: ((altWord a b (pairOrder S a b)).tail ++ ζab) ++ η))
      ((D.bracket a b ++ D.bracket b c ++ D.bracket c a) ++
        D.pathW (a :: ((altWord a b (pairOrder S a b)).tail ++ ζab) ++ η)) := h1
  have h3 : Homotopic (pairOrder S) (a :: D.bt a) (a :: D.bt a) []
      (D.bracket a b ++ D.bracket b c ++ D.bracket c a) :=
    Homotopic.cancel_right hm h1' (IsBraidPath.nil _) ((hbab.append hbbc).append hbca) hpx
  have hclen : (c :: uc).length = n + 1 :=
    (hc.1.length_eq_length ha.1 (hc.2.trans ha.2.symm)).trans hlen
  have h4 := (D.homotopic_bracket_reverse hS2 hex hIH hca hc ha hclen).symm.append_left
    (hbab.append hbbc)
  have h5 := h3.symm.append_right hbac
  rw [List.append_nil] at h4
  rw [List.nil_append] at h5
  rw [← List.append_assoc] at h4
  exact h4.trans h5

omit hS2 hex in
open _root_.Classical in
private noncomputable def StepData.bracketFrom (D : StepData S w) (s₀ s : S) :
    List (BraidMove S) :=
  if s = s₀ then [] else D.bracket s₀ s

omit hS2 hex in
private noncomputable def StepData.tau (D : StepData S w) (s₀ : S) :
    List S → List (BraidMove S)
  | [] => []
  | s :: u => D.bracketFrom s₀ s ++ D.path s u

omit hex in
private theorem StepData.isBraidPath_bracketFrom (D : StepData S w) {s₀ s : S} {u₀ u : List S}
    (h₀ : s₀ :: u₀ ∈ reducedWords S w) (hs : s :: u ∈ reducedWords S w) :
    IsBraidPath (pairOrder S) (s₀ :: D.bt s₀) (D.bracketFrom s₀ s) (s :: D.bt s) := by
  unfold StepData.bracketFrom
  split_ifs with h
  · subst h
    rfl
  · exact D.isBraidPath_bracket hS2 (Ne.symm h) h₀ hs

private theorem StepData.homotopic_bracketFrom (D : StepData S w) (htriple : TriplePrefix S)
    {n : ℕ} (hIH : AllHomotopic (S := S) n) {s₀ s t : S} {u₀ u v : List S} (hst : s ≠ t)
    (h₀ : s₀ :: u₀ ∈ reducedWords S w) (hs : s :: u ∈ reducedWords S w)
    (ht : t :: v ∈ reducedWords S w) (hlen : (s₀ :: u₀).length = n + 1) :
    Homotopic (pairOrder S) (s₀ :: D.bt s₀) (t :: D.bt t)
      (D.bracketFrom s₀ s ++ D.bracket s t) (D.bracketFrom s₀ t) := by
  have hslen : (s :: u).length = n + 1 :=
    (hs.1.length_eq_length h₀.1 (hs.2.trans h₀.2.symm)).trans hlen
  unfold StepData.bracketFrom
  by_cases h1 : s = s₀
  · subst h1
    rw [ite_eq_left rfl, ite_eq_right (Ne.symm hst), List.nil_append]
  · by_cases h2 : t = s₀
    · subst h2
      rw [ite_eq_right h1, ite_eq_left rfl]
      exact D.homotopic_bracket_reverse hS2 hex hIH (Ne.symm h1) h₀ hs hlen
    · rw [ite_eq_right h1, ite_eq_right h2]
      exact D.homotopic_bracket_triangle hS2 hex htriple hIH (Ne.symm h1) hst h2 h₀ hs ht hlen

private theorem StepData.homotopic_tau_move (D : StepData S w) (htriple : TriplePrefix S)
    {n : ℕ} (hIH : AllHomotopic (S := S) n) {s₀ : S} {u₀ : List S}
    (h₀ : s₀ :: u₀ ∈ reducedWords S w) (hlen₀ : (s₀ :: u₀).length = n + 1) {e : BraidMove S}
    (he : e.IsValid (pairOrder S)) (hx : e.source ∈ reducedWords S w) :
    Homotopic (pairOrder S) (s₀ :: D.bt s₀) e.target (D.tau s₀ e.source ++ [e])
      (D.tau s₀ e.target) := by
  have hlen : e.source.length = n + 1 :=
    (hx.1.length_eq_length h₀.1 (hx.2.trans h₀.2.symm)).trans hlen₀
  have hy := mem_reducedWords_target hS2 he hx
  have hw := D.homotopic_walk hS2 hex hIH hx hlen (IsBraidPath.singleton he)
  obtain ⟨pre, s, t, K, η⟩ := e
  cases pre with
  | nil =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.2.2
    have hst : s ≠ t := he.1
    have hxs : s :: (altWord t s k ++ η) ∈ reducedWords S w := hx
    have hyt : t :: (altWord s t k ++ η) ∈ reducedWords S w := hy
    have hw' : Homotopic (pairOrder S) (s :: D.bt s) (t :: (altWord s t k ++ η))
        (D.path s (altWord t s k ++ η) ++ [⟨[], s, t, k + 1, η⟩])
        ((D.bracket s t ++ []) ++ D.path t (altWord s t k ++ η)) := hw
    rw [List.append_nil] at hw'
    have t1 := hw'.append_left (D.isBraidPath_bracketFrom hS2 h₀ hxs)
    have t2 := (D.homotopic_bracketFrom hS2 hex htriple hIH hst h₀ hxs hyt hlen₀).append_right
      (D.isBraidPath_path hyt)
    rw [List.append_assoc] at t2
    change Homotopic (pairOrder S) (s₀ :: D.bt s₀) (t :: (altWord s t k ++ η))
      (D.bracketFrom s₀ s ++ D.path s (altWord t s k ++ η) ++ [⟨[], s, t, k + 1, η⟩])
      (D.bracketFrom s₀ t ++ D.path t (altWord s t k ++ η))
    rw [List.append_assoc (D.bracketFrom s₀ s)]
    exact t1.trans t2
  | cons a pre' =>
    have hxa : a :: (pre' ++ altWord s t K ++ η) ∈ reducedWords S w := hx
    have hw' : Homotopic (pairOrder S) (a :: D.bt a) (a :: (pre' ++ altWord t s K ++ η))
        (D.path a (pre' ++ altWord s t K ++ η) ++ [⟨a :: pre', s, t, K, η⟩])
        (D.path a (pre' ++ altWord t s K ++ η)) := hw
    have t1 := hw'.append_left (D.isBraidPath_bracketFrom hS2 h₀ hxa)
    change Homotopic (pairOrder S) (s₀ :: D.bt s₀) (a :: (pre' ++ altWord t s K ++ η))
      (D.bracketFrom s₀ a ++ D.path a (pre' ++ altWord s t K ++ η) ++ [⟨a :: pre', s, t, K, η⟩])
      (D.bracketFrom s₀ a ++ D.path a (pre' ++ altWord t s K ++ η))
    rw [List.append_assoc (D.bracketFrom s₀ a)]
    exact t1

private theorem StepData.homotopic_tau (D : StepData S w) (htriple : TriplePrefix S)
    {n : ℕ} (hIH : AllHomotopic (S := S) n) {s₀ : S} {u₀ : List S}
    (h₀ : s₀ :: u₀ ∈ reducedWords S w) (hlen₀ : (s₀ :: u₀).length = n + 1) {x y : List S}
    {γ : List (BraidMove S)} (hx : x ∈ reducedWords S w) (hγ : IsBraidPath (pairOrder S) x γ y) :
    Homotopic (pairOrder S) (s₀ :: D.bt s₀) y (D.tau s₀ x ++ γ) (D.tau s₀ y) := by
  induction γ generalizing x with
  | nil =>
    rw [isBraidPath_nil] at hγ
    subst hγ
    rw [List.append_nil]
  | cons e γ ih =>
    obtain ⟨he, rfl, hγ'⟩ := hγ
    have h1 := (D.homotopic_tau_move hS2 hex htriple hIH h₀ hlen₀ he hx).append_right hγ'
    have h2 := ih (mem_reducedWords_target hS2 he hx) hγ'
    rw [List.append_assoc, List.singleton_append] at h1
    exact h1.trans h2

omit hex in
private theorem StepData.isBraidPath_tau (D : StepData S w) {s₀ : S} {u₀ : List S}
    (h₀ : s₀ :: u₀ ∈ reducedWords S w) {x : List S} (hx : x ∈ reducedWords S w) (hne : x ≠ []) :
    IsBraidPath (pairOrder S) (s₀ :: D.bt s₀) (D.tau s₀ x) x := by
  obtain ⟨s, u, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact (D.isBraidPath_bracketFrom hS2 h₀ hx).append (D.isBraidPath_path hx)

omit hS2 hex in
private theorem eq_nil_of_isBraidPath_nil {m : B → B → ℕ} {γ : List (BraidMove B)} {y : List B}
    (h : IsBraidPath m [] γ y) : γ = [] := by
  cases γ with
  | nil => rfl
  | cons e γ =>
    exfalso
    have h1 := congrArg List.length h.2.1
    simp only [BraidMove.source, List.length_append, length_altWord, List.length_nil] at h1
    exact h.1.2.2 (by omega)

private theorem allHomotopic_succ (htriple : TriplePrefix S) {n : ℕ}
    (hIH : AllHomotopic (S := S) n) : AllHomotopic (S := S) (n + 1) := by
  intro x y hx hlen γ γ' hγ hγ'
  obtain ⟨D⟩ := StepData.nonempty hS2 hex (wordProd S x)
  have hxw : x ∈ reducedWords S (wordProd S x) := ⟨hx, rfl⟩
  obtain ⟨s₀, u₀, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  refine homotopic_of_forall_closed (pairOrder_comm hS2) (fun c hc => ?_) hγ hγ'
  have hτ := D.isBraidPath_tau hS2 hxw hxw (List.cons_ne_nil _ _)
  have h1 := D.homotopic_tau hS2 hex htriple hIH hxw hlen hxw hc
  have h1' : Homotopic (pairOrder S) (s₀ :: D.bt s₀) (s₀ :: u₀) (D.tau s₀ (s₀ :: u₀) ++ c)
      (D.tau s₀ (s₀ :: u₀) ++ []) := by
    rw [List.append_nil]
    exact h1
  exact Homotopic.cancel_left (pairOrder_comm hS2) h1' hτ hc (IsBraidPath.nil _)

private theorem allHomotopic (htriple : TriplePrefix S) : ∀ n, AllHomotopic (S := S) n
  | 0 => fun x y hx hlen γ γ' hγ hγ' => by
    obtain rfl := List.length_eq_zero_iff.1 hlen
    rw [eq_nil_of_isBraidPath_nil hγ, eq_nil_of_isBraidPath_nil hγ']
  | n + 1 => allHomotopic_succ hS2 hex htriple (allHomotopic htriple n)

end Step

section Main

variable (hS2 : ∀ s ∈ S, orderOf s = 2)
include hS2

theorem IsBraidPath.mem_reducedWords {w : W} {x y : List S} {γ : List (BraidMove S)}
    (hx : x ∈ reducedWords S w) (hγ : IsBraidPath (pairOrder S) x γ y) :
    y ∈ reducedWords S w ∧
      ∀ e ∈ γ, e.source ∈ reducedWords S w ∧ e.target ∈ reducedWords S w := by
  refine ⟨⟨hγ.isReduced hS2 hx.1, (hγ.wordProd_eq hS2).trans hx.2⟩, fun e he => ?_⟩
  obtain ⟨h1, h2⟩ := hγ.isReduced_source hS2 hx.1 e he
  have hs : e.source ∈ reducedWords S w := ⟨h1, h2.trans hx.2⟩
  exact ⟨hs, mem_reducedWords_target hS2 (hγ.isValid_of_mem he) hs⟩

variable (hex : ExchangeCondition S)
include hex

theorem pairPrefix_of_exchangeCondition : PairPrefix S := by
  intro w s t hst hs ht
  have hw : ∃ l : List S, wordProd S l = w := by
    by_contra hne
    have h0 : {n | ∃ l : List S, l.length = n ∧ wordProd S l = w} = ∅ :=
      Set.eq_empty_of_forall_notMem fun n ⟨l, _, hl⟩ => hne ⟨l, hl⟩
    have h1 : wordLength S w = 0 := by
      change sInf {n | ∃ l : List S, l.length = n ∧ wordProd S l = w} = 0
      rw [h0, Nat.sInf_empty]
    have hs' : wordLength S ((s : W) * w) < wordLength S w := hs
    rw [h1] at hs'
    exact Nat.not_lt_zero _ hs'
  obtain ⟨l, rfl⟩ := hw
  obtain ⟨l', hl', hl'p⟩ := exists_isReduced_wordProd_eq l
  rw [← hl'p] at hs ht ⊢
  obtain ⟨-, σ, hA, hAp⟩ := exists_isReduced_altWord_append hS2 hex hl' hs ht
  change IsReduced S (altWord s t (orderOf ((s : W) * t))) ∧
    wordLength S ((wordProd S (altWord s t (orderOf ((s : W) * t))))⁻¹ * wordProd S l') =
      wordLength S (wordProd S l') - orderOf ((s : W) * t)
  refine ⟨hA.of_append_left, ?_⟩
  have h1 : (wordProd S (altWord s t (orderOf ((s : W) * t))))⁻¹ * wordProd S l' =
      wordProd S σ := by
    rw [← hAp, wordProd_append, inv_mul_cancel_left]
  rw [h1, ← hA.of_append_right.length_eq, ← hAp, ← hA.length_eq, List.length_append,
    length_altWord]
  omega

theorem homotopic_of_isReduced (htriple : TriplePrefix S) {x y : List S} (hx : IsReduced S x)
    {γ γ' : List (BraidMove S)} (hγ : IsBraidPath (pairOrder S) x γ y)
    (hγ' : IsBraidPath (pairOrder S) x γ' y) : Homotopic (pairOrder S) x y γ γ' :=
  allHomotopic hS2 hex htriple x.length x y hx rfl γ γ' hγ hγ'

theorem reduced_word_rank_three_coherence (htriple : TriplePrefix S) {w : W} {x y : List S}
    (hx : x ∈ reducedWords S w) (hy : y ∈ reducedWords S w) :
    (∃ γ, IsBraidPath (pairOrder S) x γ y) ∧
      (∀ γ γ', IsBraidPath (pairOrder S) x γ y → IsBraidPath (pairOrder S) x γ' y →
        Homotopic (pairOrder S) x y γ γ') ∧
      ∀ γ, IsBraidPath (pairOrder S) x γ x → Homotopic (pairOrder S) x x γ [] :=
  ⟨exists_isBraidPath hS2 hex hx.1 hy.1 (hx.2.trans hy.2.symm),
    fun _ _ hγ hγ' => homotopic_of_isReduced hS2 hex htriple hx.1 hγ hγ',
    fun _ hγ => homotopic_of_isReduced hS2 hex htriple hx.1 hγ (IsBraidPath.nil x)⟩

end Main

end Group

end CFSG.Monster.B.Geometry
