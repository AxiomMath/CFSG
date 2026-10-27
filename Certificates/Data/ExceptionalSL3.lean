module

public import Certificates.Data.ExceptionalF9
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG

namespace Glauberman.Dickson

open Matrix
open QuadraticAlgebra

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

@[expose] abbrev ExceptionalSL3 :=
  Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

@[expose] def exceptionalSL3Y : ExceptionalSL3 :=
  ⟨!![1, 0; 1, 1], by decide⟩

@[expose] def exceptionalSL3Z5 : ExceptionalSL5 :=
  ⟨!![1, 1; 3, 4], by decide⟩

@[expose] def exceptionalSL3MatrixKey (g : ExceptionalSL3) : Nat :=
  (g.1 0 0).val + 3 * (g.1 0 1).val +
    9 * (g.1 1 0).val + 27 * (g.1 1 1).val

@[expose] def exceptionalSL3WordCode : Nat → Nat × Nat
  | 15 => (1, 1)
  | 16 => (1, 3)
  | 17 => (1, 2)
  | 21 => (7, 3)
  | 22 => (13, 4)
  | 23 => (10, 4)
  | 28 => (0, 0)
  | 31 => (26, 5)
  | 34 => (4, 5)
  | 37 => (0, 1)
  | 41 => (20, 5)
  | 42 => (4, 3)
  | 46 => (0, 2)
  | 48 => (14, 4)
  | 53 => (4, 4)
  | 56 => (3, 2)
  | 59 => (5, 3)
  | 62 => (2, 3)
  | 65 => (12, 4)
  | 67 => (5, 5)
  | 69 => (2, 2)
  | 74 => (6, 3)
  | 75 => (5, 4)
  | 79 => (2, 4)
  | _ => (0, 0)

@[expose] def evalExceptionalSL3Code {G : Type*} [Group G]
    (Y Z : G) : Nat → Nat → G
  | _, 0 => 1
  | code, n + 1 =>
      (if code % 2 = 0 then Y else Z) *
        evalExceptionalSL3Code Y Z (code / 2) n

@[expose] def exceptionalSL3Fn (g : ExceptionalSL3) : ExceptionalSL5 :=
  let code := exceptionalSL3WordCode (exceptionalSL3MatrixKey g)
  evalExceptionalSL3Code exceptionalY5 exceptionalSL3Z5 code.1 code.2

end Glauberman.Dickson

end CFSG
