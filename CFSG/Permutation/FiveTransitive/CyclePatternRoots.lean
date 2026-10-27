module

public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG

namespace FiveTransitive.CyclePatternRoots

open Equiv

variable {X : Type*}

@[expose] abbrev Pattern {I : Type*} (g : Perm X) (π : Perm I) :=
  {e : I ↪ X // ∀ i, g (e i) = e (π i)}

@[expose] abbrev TwoRoot (g : Perm X) := {x : X // g (g x) = x ∧ g x ≠ x}
@[expose] abbrev FourRoot (g : Perm X) := {x : X // g (g (g (g x))) = x ∧ g (g x) ≠ x}

@[expose] def twoEquiv (g : Perm X) : Pattern g (finRotate 2) ≃ TwoRoot g where
  toFun e := ⟨e.val 0, by
    have h0 : g (e.val 0) = e.val 1 := e.property 0
    have h1 : g (e.val 1) = e.val 0 := e.property 1
    exact ⟨by rw [h0,h1], by rw [h0]; exact e.val.injective.ne (by decide)⟩⟩
  invFun x := ⟨⟨![x.val, g x.val], by
    intro i j; fin_cases i <;> fin_cases j <;> simp [x.property.2, x.property.2.symm]⟩, by
    intro i; fin_cases i
    · rfl
    · exact x.property.1⟩
  left_inv e := by
    apply Subtype.ext
    ext i; fin_cases i
    · rfl
    · exact e.property 0
  right_inv x := rfl

@[expose] def fourEquiv (g : Perm X) : Pattern g (finRotate 4) ≃ FourRoot g where
  toFun e := ⟨e.val 0, by
    have h0 : g (e.val 0) = e.val 1 := e.property 0
    have h1 : g (e.val 1) = e.val 2 := e.property 1
    have h2 : g (e.val 2) = e.val 3 := e.property 2
    have h3 : g (e.val 3) = e.val 0 := e.property 3
    exact ⟨by rw [h0,h1,h2,h3], by rw [h0,h1]; exact e.val.injective.ne (by decide)⟩⟩
  invFun x := ⟨⟨![x.val, g x.val, g (g x.val), g (g (g x.val))], by
    have h01 : x.val ≠ g x.val := by
      intro h
      exact x.property.2 ((congrArg g h.symm).trans h.symm)
    have h02 : x.val ≠ g (g x.val) := x.property.2.symm
    have h12 : g x.val ≠ g (g x.val) := g.injective.ne h01
    have h13 : g x.val ≠ g (g (g x.val)) := g.injective.ne h02
    have h23 : g (g x.val) ≠ g (g (g x.val)) := g.injective.ne h12
    have h03 : x.val ≠ g (g (g x.val)) := by
      intro h
      have hh := congrArg g h
      rw [x.property.1] at hh
      exact h01 hh.symm
    intro i j
    fin_cases i <;> fin_cases j <;> simp [h01,h02,h03,h12,h13,h23,eq_comm]⟩, by
    intro i; fin_cases i
    · rfl
    · rfl
    · rfl
    · exact x.property.1⟩
  left_inv e := by
    have h0 : g (e.val 0) = e.val 1 := e.property 0
    have h1 : g (e.val 1) = e.val 2 := e.property 1
    have h2 : g (e.val 2) = e.val 3 := e.property 2
    apply Subtype.ext
    ext i; fin_cases i
    · rfl
    · exact h0
    · exact (congrArg g h0).trans h1
    · exact (congrArg g ((congrArg g h0).trans h1)).trans h2
  right_inv x := rfl

theorem card_two_pattern [Finite X] (g : Perm X) :
    Nat.card (Pattern g (finRotate 2)) = Nat.card (TwoRoot g) :=
  Nat.card_congr (twoEquiv g)

theorem card_four_pattern [Finite X] (g : Perm X) :
    Nat.card (Pattern g (finRotate 4)) = Nat.card (FourRoot g) :=
  Nat.card_congr (fourEquiv g)

end FiveTransitive.CyclePatternRoots

end CFSG
