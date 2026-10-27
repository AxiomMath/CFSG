module

public import CFSG.Monster.B.GSide.HomotopyTyped

public section

namespace CFSG.Monster.B.GSide

open SimpleGraph

inductive WStep (V : Type*) where
  | ins (i : ℕ) (b : V)
  | del (i : ℕ)
  | bins (i : ℕ) (b : V)
  | bdel (i : ℕ)

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  (T : V → V → V → Prop) [∀ x y z, Decidable (T x y z)]

@[expose] def walkStep : {u v : V} → G.Walk u v → WStep V → Option (G.Walk u v)
  | x, _, .cons (v := y) _ p, .ins 0 b =>
      if h₁ : G.Adj x b then if h₂ : G.Adj b y then if T x b y then
        some (.cons h₁ (.cons h₂ p)) else none else none else none
  | _, _, .cons h p, .ins (i + 1) b => (walkStep p (.ins i b)).map (.cons h)
  | x, _, .cons (v := b) _ (.cons (v := y) _ p), .del 0 =>
      if h : G.Adj x y then if T x b y then some (.cons h p) else none else none
  | _, _, .cons h p, .del (i + 1) => (walkStep p (.del i)).map (.cons h)
  | u, _, p, .bins 0 b => if h : G.Adj u b then some (.cons h (.cons h.symm p)) else none
  | _, _, .cons h p, .bins (i + 1) b => (walkStep p (.bins i b)).map (.cons h)
  | u, _, .cons _ (.cons (v := w) _ p), .bdel 0 =>
      if hw : w = u then some (p.copy hw rfl) else none
  | _, _, .cons h p, .bdel (i + 1) => (walkStep p (.bdel i)).map (.cons h)
  | _, _, _, _ => none

theorem homotopicT_of_walkStep {u v : V} {p q : G.Walk u v} {s : WStep V}
    (h : walkStep T p s = some q) : HomotopicT T p q := by
  induction p generalizing s with
  | nil =>
    cases s with
    | ins i b => cases i <;> simp [walkStep] at h
    | del i => cases i <;> simp [walkStep] at h
    | bins i b =>
      cases i with
      | zero =>
        simp only [walkStep] at h
        split_ifs at h with hb
        cases h
        exact (homotopicT_cons_cons hb _).symm
      | succ i => simp [walkStep] at h
    | bdel i => cases i <;> simp [walkStep] at h
  | @cons x y w hxy p ih =>
    cases s with
    | ins i b =>
      cases i with
      | zero =>
        simp only [walkStep] at h
        split_ifs at h with h₁ h₂ hT
        cases h
        simpa using homotopicT_edge_triangle (T := T) (.nil : G.Walk x x) p hxy h₁ h₂ hT
      | succ i =>
        simp only [walkStep, Option.map_eq_some_iff] at h
        obtain ⟨q', hq', rfl⟩ := h
        exact (ih hq').cons hxy
    | del i =>
      cases i with
      | zero =>
        cases p with
        | nil => simp [walkStep] at h
        | cons hyz p =>
          simp only [walkStep] at h
          split_ifs at h with h₁ hT
          cases h
          simpa using
            (homotopicT_edge_triangle (T := T) (.nil : G.Walk x x) p h₁ hxy hyz hT).symm
      | succ i =>
        simp only [walkStep, Option.map_eq_some_iff] at h
        obtain ⟨q', hq', rfl⟩ := h
        exact (ih hq').cons hxy
    | bins i b =>
      cases i with
      | zero =>
        simp only [walkStep] at h
        split_ifs at h with hb
        cases h
        exact (homotopicT_cons_cons hb _).symm
      | succ i =>
        simp only [walkStep, Option.map_eq_some_iff] at h
        obtain ⟨q', hq', rfl⟩ := h
        exact (ih hq').cons hxy
    | bdel i =>
      cases i with
      | zero =>
        cases p with
        | nil => simp [walkStep] at h
        | cons hyz p =>
          simp only [walkStep] at h
          split_ifs at h with hw
          cases h
          subst hw
          simpa using homotopicT_cons_cons (T := T) hxy p
      | succ i =>
        simp only [walkStep, Option.map_eq_some_iff] at h
        obtain ⟨q', hq', rfl⟩ := h
        exact (ih hq').cons hxy

@[expose] def walkSteps {u v : V} (p : G.Walk u v) : List (WStep V) → Option (G.Walk u v)
  | [] => some p
  | s :: ss => (walkStep T p s).bind fun q => walkSteps q ss

theorem homotopicT_of_walkSteps {u v : V} {p q : G.Walk u v} {ss : List (WStep V)}
    (h : walkSteps T p ss = some q) : HomotopicT T p q := by
  induction ss generalizing p with
  | nil =>
    simp only [walkSteps, Option.some.injEq] at h
    subst h
    exact HomotopicT.refl _
  | cons s ss ih =>
    simp only [walkSteps, Option.bind_eq_some_iff] at h
    obtain ⟨q', h₁, h₂⟩ := h
    exact (homotopicT_of_walkStep T h₁).trans (ih h₂)

theorem homotopicT_nil_of_walkSteps {u : V} {p q : G.Walk u u} {ss : List (WStep V)}
    (h : walkSteps T p ss = some q) (hq : q.length = 0) : HomotopicT T p .nil := by
  have e : q = .nil := Walk.eq_nil_iff_nil.2 (Walk.length_eq_zero_iff.1 hq)
  exact e ▸ homotopicT_of_walkSteps T h

end CFSG.Monster.B.GSide
