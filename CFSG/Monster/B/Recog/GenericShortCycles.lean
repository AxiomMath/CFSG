module

public import CFSG.Monster.B.Recog.GenericWalkHomotopy
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Monster.B.Recog

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

@[expose] def walkProd {b : V} (L : List (G.Walk b b)) : G.Walk b b :=
  L.foldr (fun q r => q.append r) .nil

@[simp] theorem walkProd_nil {b : V} : walkProd ([] : List (G.Walk b b)) = .nil := rfl

@[simp] theorem walkProd_cons {b : V} (q : G.Walk b b) (L : List (G.Walk b b)) :
    walkProd (q :: L) = q.append (walkProd L) := rfl

theorem homotopic_walkProd_nil {b : V} {L : List (G.Walk b b)}
    (h : ∀ q ∈ L, Homotopic q .nil) : Homotopic (walkProd L) .nil := by
  induction L with
  | nil => exact Homotopic.refl _
  | cons q L ih =>
    simpa using (h q List.mem_cons_self).append
      (ih fun r hr => h r (List.mem_cons_of_mem q hr))

@[expose] def lasso {b : V} (γ : ∀ x, G.Walk b x) {x y : V} (h : G.Adj x y) : G.Walk b b :=
  (γ x).append (.cons h (γ y).reverse)

theorem homotopic_foldr_lasso {b : V} (γ : ∀ x, G.Walk b x) :
    ∀ {x y : V} (p : G.Walk x y), ∃ L : List (G.Walk b b),
      (∀ q ∈ L, ∃ (x' y' : V) (h : G.Adj x' y'), q = lasso γ h) ∧
      Homotopic ((γ x).append (p.append (γ y).reverse)) (walkProd L)
  | x, _, .nil => ⟨[], by simp, by simpa using homotopic_append_reverse (γ x)⟩
  | x, y, .cons (v := x') h p => by
    obtain ⟨L, hL, hp⟩ := homotopic_foldr_lasso γ p
    refine ⟨lasso γ h :: L, fun q hq => ?_, ?_⟩
    · rcases List.mem_cons.1 hq with rfl | hq
      · exact ⟨x, x', h, rfl⟩
      · exact hL q hq
    · set R := (γ x').append (p.append (γ y).reverse) with hR
      have h₁ : Homotopic ((γ x').reverse.append R) (p.append (γ y).reverse) := by
        have := (homotopic_reverse_append (γ x')).append_right (p.append (γ y).reverse)
        rwa [Walk.nil_append, ← Walk.append_assoc] at this
      have e : (lasso γ h).append R = (γ x).append (.cons h ((γ x').reverse.append R)) := by
        rw [lasso, ← Walk.append_assoc, Walk.cons_append]
      rw [walkProd_cons]
      refine ((h₁.symm.cons h).append_left (γ x)).trans ?_
      rw [← e]
      exact hp.append_left (lasso γ h)

end CFSG.Monster.B.Recog
