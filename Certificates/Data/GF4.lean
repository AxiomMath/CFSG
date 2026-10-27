module

public import Mathlib

public section

namespace Certificates.A5GL42

structure GF4 where
  c : ZMod 2
  d : ZMod 2

@[expose] instance : DecidableEq GF4 := fun x y =>
  if h : x.c = y.c ∧ x.d = y.d then
    isTrue (by cases x; cases y; simp_all)
  else
    isFalse (by intro e; subst e; exact h ⟨rfl, rfl⟩)

@[expose] instance : Fintype GF4 where
  elems := {⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩}
  complete := by
    intro x
    cases x with
    | mk c d => fin_cases c <;> fin_cases d <;> decide

namespace GF4

@[expose] def add (x y : GF4) : GF4 := ⟨x.c + y.c, x.d + y.d⟩

@[expose] def mul (x y : GF4) : GF4 := ⟨x.c * y.c + x.d * y.d, x.c * y.d + x.d * y.c + x.d * y.d⟩

@[expose] def inv (x : GF4) : GF4 := mul x x

@[expose] instance : Field GF4 :=
  letI : Add GF4 := ⟨add⟩
  letI : Mul GF4 := ⟨mul⟩
  letI : Neg GF4 := ⟨fun x => x⟩
  letI : Inv GF4 := ⟨inv⟩
  letI : Zero GF4 := ⟨⟨0, 0⟩⟩
  letI : One GF4 := ⟨⟨1, 0⟩⟩
  Field.ofMinimalAxioms GF4
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ⟨0, 1, by decide⟩

end GF4

end Certificates.A5GL42
