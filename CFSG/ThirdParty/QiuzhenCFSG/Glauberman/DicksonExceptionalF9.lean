module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public meta import Mathlib.Algebra.QuadraticAlgebra.Defs
public meta import Mathlib.Algebra.Field.ZMod
public meta import Mathlib.Data.ZMod.Defs
public meta import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The exceptional two-transvection subgroups over `F₉`

This module supplies the two finite calculations needed in the exceptional
`A₅` branch of Dickson's subgroup classification.  The concrete field is
`F₃[ω]/(ω²+1)`.

* For `r = ω`, the two standard transvections generate the binary
  icosahedral subgroup, explicitly identified with `SL(2,5)`.
* For `r = ω-1`, they generate all of `SL(2,9)`.

The `SL(2,5)` identification is certified by a normal-word table for the
generating pair `[[0,1],[-1,-1]]`, `[[0,-1],[1,-1]]`.  There are 120 entries
and every word has length at most ten.  A cached table of the corresponding
target matrices lets kernel `decide` validate multiplication by each
generator and the trivial kernel without repeatedly evaluating the words;
the full homomorphism law and agreement with the words then follow by
induction.  The public theorems transport these concrete certificates to
arbitrary fields of order nine.
-/

namespace CFSG.Glauberman
namespace Dickson

open QuadraticAlgebra

private local instance f9_irreducible :
    Fact (∀ r : ZMod 3, r ^ 2 ≠ (-1 : ZMod 3) + 0 * r) := ⟨by decide⟩

public abbrev ExceptionalF9 := QuadraticAlgebra (ZMod 3) (-1) 0
public abbrev ExceptionalSL5 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)
public abbrev ExceptionalSL9 := Matrix.SpecialLinearGroup (Fin 2) ExceptionalF9

local instance : Fintype ExceptionalF9 :=
  Fintype.ofEquiv (ZMod 3 × ZMod 3)
    (QuadraticAlgebra.equivProd (-1 : ZMod 3) 0).symm

public def exceptionalX5 : ExceptionalSL5 := ⟨!![0, 1; 4, 4], by decide⟩
@[expose] public def exceptionalY5 : ExceptionalSL5 := ⟨!![0, 4; 1, 4], by decide⟩

@[expose] public def exceptionalX9 : ExceptionalSL9 :=
  ⟨!![1, ω; 0, 1], by simp [Matrix.det_fin_two]⟩
@[expose] public def exceptionalY9 : ExceptionalSL9 :=
  ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

private def secondRootF9 : ExceptionalF9 := ω - 1
private def secondRootX9 : ExceptionalSL9 :=
  ⟨!![1, secondRootF9; 0, 1], by simp [Matrix.det_fin_two]⟩

private def exceptionalMatrixKey (g : ExceptionalSL5) : Nat :=
  (g.1 0 0).val + 5 * (g.1 0 1).val +
    25 * (g.1 1 0).val + 125 * (g.1 1 1).val

/-- A compact normal-word certificate for the concrete generating pair of
`SL(2,5)`.  The first component stores the `X/Y` bits, least-significant bit
first; the second stores the word length. -/
private def exceptionalWordCode : Nat → Nat × Nat
  | 45 => (73, 7)
  | 46 => (148, 9)
  | 47 => (45, 6)
  | 48 => (27, 5)
  | 49 => (0, 2)
  | 60 => (77, 8)
  | 61 => (25, 6)
  | 62 => (10, 4)
  | 63 => (102, 9)
  | 64 => (44, 7)
  | 90 => (178, 8)
  | 91 => (38, 6)
  | 92 => (5, 4)
  | 93 => (204, 9)
  | 94 => (26, 7)
  | 105 => (54, 7)
  | 106 => (330, 9)
  | 107 => (18, 6)
  | 108 => (4, 5)
  | 109 => (3, 2)
  | 126 => (0, 0)
  | 131 => (36, 6)
  | 136 => (82, 7)
  | 141 => (45, 7)
  | 146 => (27, 6)
  | 151 => (54, 6)
  | 157 => (3, 4)
  | 163 => (4, 4)
  | 169 => (18, 5)
  | 170 => (165, 8)
  | 176 => (90, 7)
  | 183 => (13, 4)
  | 185 => (11, 6)
  | 192 => (12, 6)
  | 199 => (9, 5)
  | 201 => (37, 7)
  | 209 => (22, 5)
  | 212 => (51, 6)
  | 215 => (52, 6)
  | 223 => (2, 4)
  | 226 => (9, 6)
  | 230 => (90, 8)
  | 239 => (13, 5)
  | 243 => (11, 4)
  | 247 => (12, 4)
  | 253 => (10, 5)
  | 258 => (102, 7)
  | 263 => (44, 8)
  | 268 => (154, 8)
  | 273 => (25, 7)
  | 278 => (76, 7)
  | 281 => (1, 2)
  | 289 => (41, 6)
  | 292 => (75, 7)
  | 295 => (218, 8)
  | 303 => (89, 8)
  | 309 => (26, 6)
  | 310 => (204, 8)
  | 316 => (5, 3)
  | 322 => (105, 7)
  | 328 => (52, 8)
  | 332 => (22, 7)
  | 336 => (2, 3)
  | 340 => (51, 8)
  | 349 => (37, 6)
  | 353 => (51, 7)
  | 355 => (164, 8)
  | 362 => (52, 7)
  | 369 => (22, 6)
  | 371 => (2, 2)
  | 377 => (204, 10)
  | 382 => (26, 5)
  | 387 => (89, 7)
  | 392 => (38, 7)
  | 397 => (5, 5)
  | 402 => (20, 5)
  | 409 => (180, 9)
  | 411 => (19, 5)
  | 418 => (50, 6)
  | 420 => (6, 4)
  | 427 => (50, 7)
  | 431 => (6, 5)
  | 435 => (20, 6)
  | 444 => (153, 8)
  | 448 => (19, 6)
  | 452 => (77, 7)
  | 458 => (44, 6)
  | 464 => (102, 8)
  | 465 => (10, 6)
  | 471 => (25, 5)
  | 477 => (11, 5)
  | 480 => (9, 4)
  | 488 => (13, 6)
  | 491 => (12, 5)
  | 499 => (90, 9)
  | 504 => (660, 10)
  | 509 => (18, 7)
  | 514 => (4, 3)
  | 519 => (3, 3)
  | 524 => (109, 7)
  | 529 => (91, 7)
  | 533 => (74, 8)
  | 537 => (210, 8)
  | 541 => (100, 7)
  | 545 => (1, 1)
  | 554 => (6, 3)
  | 557 => (180, 8)
  | 560 => (50, 8)
  | 568 => (20, 7)
  | 571 => (19, 7)
  | 579 => (1, 3)
  | 581 => (108, 7)
  | 588 => (74, 7)
  | 590 => (76, 8)
  | 597 => (75, 8)
  | 604 => (36, 7)
  | 605 => (0, 1)
  | 611 => (27, 7)
  | 617 => (45, 8)
  | 623 => (148, 8)
  | _ => (0, 0)

private def evalExceptionalCode {G : Type*} [Group G] (X Y : G) : Nat → Nat → G
  | _, 0 => 1
  | code, n + 1 =>
      (if code % 2 = 0 then X else Y) *
        evalExceptionalCode X Y (code / 2) n

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private def exceptionalImageTable : Nat → ExceptionalSL9
  | 45 => ⟨!![0, 2 + ω; 2 + 2 * ω, 0], by decide⟩
  | 46 => ⟨!![2, 0; 1, 2], by decide⟩
  | 47 => ⟨!![2 + ω, 1 + 2 * ω; 2, 2 + ω], by decide⟩
  | 48 => ⟨!![1 + 2 * ω, ω; 1 + ω, 1 + 2 * ω], by decide⟩
  | 49 => ⟨!![1, 2 * ω; 0, 1], by decide⟩
  | 60 => ⟨!![2 * ω, 0; 0, ω], by decide⟩
  | 61 => ⟨!![1 + ω, 2; ω, 2 * ω], by decide⟩
  | 62 => ⟨!![0, 2 + 2 * ω; 2 + ω, 1 + ω], by decide⟩
  | 63 => ⟨!![2 + 2 * ω, 1 + ω; 1 + 2 * ω, 0], by decide⟩
  | 64 => ⟨!![ω, 1; 2 * ω, 2 + 2 * ω], by decide⟩
  | 90 => ⟨!![ω, 0; 0, 2 * ω], by decide⟩
  | 91 => ⟨!![2 * ω, 2; ω, 1 + ω], by decide⟩
  | 92 => ⟨!![1 + ω, 2 + 2 * ω; 2 + ω, 0], by decide⟩
  | 93 => ⟨!![0, 1 + ω; 1 + 2 * ω, 2 + 2 * ω], by decide⟩
  | 94 => ⟨!![2 + 2 * ω, 1; 2 * ω, ω], by decide⟩
  | 105 => ⟨!![0, 1 + 2 * ω; 1 + ω, 0], by decide⟩
  | 106 => ⟨!![2, ω; 0, 2], by decide⟩
  | 107 => ⟨!![2 + ω, 2 * ω; 2 + 2 * ω, 2 + ω], by decide⟩
  | 108 => ⟨!![1 + 2 * ω, 2 + ω; 1, 1 + 2 * ω], by decide⟩
  | 109 => ⟨!![1, 0; 2, 1], by decide⟩
  | 126 => ⟨!![1, 0; 0, 1], by decide⟩
  | 131 => ⟨!![0, 2 + ω; 2 + 2 * ω, 1 + 2 * ω], by decide⟩
  | 136 => ⟨!![2, 2 * ω; 1, 2 + ω], by decide⟩
  | 141 => ⟨!![2 + ω, ω; 2, 2], by decide⟩
  | 146 => ⟨!![1 + 2 * ω, 1 + 2 * ω; 1 + ω, 0], by decide⟩
  | 151 => ⟨!![0, 1 + 2 * ω; 1 + ω, 1 + 2 * ω], by decide⟩
  | 157 => ⟨!![1, 2 * ω; 2, 1 + ω], by decide⟩
  | 163 => ⟨!![1 + 2 * ω, 1; 1, 1 + ω], by decide⟩
  | 169 => ⟨!![2 + ω, 1; 2 + 2 * ω, 1 + 2 * ω], by decide⟩
  | 170 => ⟨!![2, 2 * ω; 0, 2], by decide⟩
  | 176 => ⟨!![2, ω; 2, 2 + ω], by decide⟩
  | 183 => ⟨!![1 + 2 * ω, ω; 2 * ω, 1 + ω], by decide⟩
  | 185 => ⟨!![1 + ω, 1; 2 * ω, 2 * ω], by decide⟩
  | 192 => ⟨!![1 + ω, 1 + ω; 2, 1 + ω], by decide⟩
  | 199 => ⟨!![1 + 2 * ω, 1; 2 + 2 * ω, 2 + ω], by decide⟩
  | 201 => ⟨!![2 + ω, 2 * ω; 1, 2], by decide⟩
  | 209 => ⟨!![2 + ω, 1 + 2 * ω; 2 * ω, 1 + 2 * ω], by decide⟩
  | 212 => ⟨!![1 + ω, 2 * ω; 1 + 2 * ω, 1 + ω], by decide⟩
  | 215 => ⟨!![2 * ω, 1; 2 * ω, 1 + ω], by decide⟩
  | 223 => ⟨!![1 + ω, 1; 1, 1 + 2 * ω], by decide⟩
  | 226 => ⟨!![1 + 2 * ω, 2 + ω; 2 + 2 * ω, 0], by decide⟩
  | 230 => ⟨!![2, 0; 2, 2], by decide⟩
  | 239 => ⟨!![1 + 2 * ω, 1 + 2 * ω; 2 * ω, 2 + ω], by decide⟩
  | 243 => ⟨!![1 + ω, ω; 2 * ω, 1 + 2 * ω], by decide⟩
  | 247 => ⟨!![1 + ω, 2 * ω; 2, 1], by decide⟩
  | 253 => ⟨!![0, 2 + 2 * ω; 2 + ω, 0], by decide⟩
  | 258 => ⟨!![2 + 2 * ω, 2; 1 + 2 * ω, 1 + ω], by decide⟩
  | 263 => ⟨!![ω, 0; 2 * ω, 2 * ω], by decide⟩
  | 268 => ⟨!![2 * ω, 1; 0, ω], by decide⟩
  | 273 => ⟨!![1 + ω, 1 + ω; ω, 2 + 2 * ω], by decide⟩
  | 278 => ⟨!![2 + 2 * ω, 1 + ω; ω, 1 + ω], by decide⟩
  | 281 => ⟨!![1, ω; 1, 1 + ω], by decide⟩
  | 289 => ⟨!![2 + 2 * ω, 1; 1, 2 + ω], by decide⟩
  | 292 => ⟨!![2 + ω, 1; ω, 2 * ω], by decide⟩
  | 295 => ⟨!![2 + ω, ω; 1 + ω, 2 + ω], by decide⟩
  | 303 => ⟨!![ω, 1; 0, 2 * ω], by decide⟩
  | 309 => ⟨!![2 + 2 * ω, ω; 2 * ω, 2 + ω], by decide⟩
  | 310 => ⟨!![0, 1 + ω; 1 + 2 * ω, 1 + ω], by decide⟩
  | 316 => ⟨!![1 + ω, ω; 2 + ω, 1 + ω], by decide⟩
  | 322 => ⟨!![2 * ω, 1; ω, 2 + ω], by decide⟩
  | 328 => ⟨!![2 * ω, 0; 2 * ω, ω], by decide⟩
  | 332 => ⟨!![2 + ω, 2; 2 * ω, 2 * ω], by decide⟩
  | 336 => ⟨!![1 + ω, 2 + 2 * ω; 1, 1 + ω], by decide⟩
  | 340 => ⟨!![1 + ω, 1 + ω; 1 + 2 * ω, 0], by decide⟩
  | 349 => ⟨!![2 + ω, 1; 1, 2 + 2 * ω], by decide⟩
  | 353 => ⟨!![1 + ω, 2; 1 + 2 * ω, 2 + 2 * ω], by decide⟩
  | 355 => ⟨!![2 + ω, 2 + ω; 1, 2 + ω], by decide⟩
  | 362 => ⟨!![2 * ω, 2; 2 * ω, 2 + ω], by decide⟩
  | 369 => ⟨!![2 + ω, ω; 2 * ω, 2 + 2 * ω], by decide⟩
  | 371 => ⟨!![1 + ω, ω; 1, 1], by decide⟩
  | 377 => ⟨!![0, 1 + ω; 1 + 2 * ω, 0], by decide⟩
  | 382 => ⟨!![2 + 2 * ω, 2 + 2 * ω; 2 * ω, 1 + ω], by decide⟩
  | 387 => ⟨!![ω, 2; 0, 2 * ω], by decide⟩
  | 392 => ⟨!![2 * ω, 0; ω, ω], by decide⟩
  | 397 => ⟨!![1 + ω, 1; 2 + ω, 2 + 2 * ω], by decide⟩
  | 402 => ⟨!![2 + 2 * ω, 1; 2 + ω, 1 + ω], by decide⟩
  | 409 => ⟨!![2 + 2 * ω, 2 * ω; 2, 2], by decide⟩
  | 411 => ⟨!![1 + 2 * ω, 2 * ω; ω, 1 + ω], by decide⟩
  | 418 => ⟨!![ω, 1; ω, 1 + 2 * ω], by decide⟩
  | 420 => ⟨!![1 + 2 * ω, 1 + 2 * ω; 2, 1 + 2 * ω], by decide⟩
  | 427 => ⟨!![ω, 0; ω, 2 * ω], by decide⟩
  | 431 => ⟨!![1 + 2 * ω, 2; 2, 1 + ω], by decide⟩
  | 435 => ⟨!![2 + 2 * ω, 2 + 2 * ω; 2 + ω, 0], by decide⟩
  | 444 => ⟨!![2 + 2 * ω, 1 + ω; 2, 2 + 2 * ω], by decide⟩
  | 448 => ⟨!![1 + 2 * ω, 1; ω, ω], by decide⟩
  | 452 => ⟨!![2 * ω, 2; 0, ω], by decide⟩
  | 458 => ⟨!![ω, 2; 2 * ω, 1 + 2 * ω], by decide⟩
  | 464 => ⟨!![2 + 2 * ω, 2 * ω; 1 + 2 * ω, 2 + 2 * ω], by decide⟩
  | 465 => ⟨!![0, 2 + 2 * ω; 2 + ω, 2 + 2 * ω], by decide⟩
  | 471 => ⟨!![1 + ω, 2 * ω; ω, 1 + 2 * ω], by decide⟩
  | 477 => ⟨!![1 + ω, 2 + 2 * ω; 2 * ω, 2 + 2 * ω], by decide⟩
  | 480 => ⟨!![1 + 2 * ω, 2 * ω; 2 + 2 * ω, 1 + 2 * ω], by decide⟩
  | 488 => ⟨!![1 + 2 * ω, 2; 2 * ω, ω], by decide⟩
  | 491 => ⟨!![1 + ω, 2; 2, 1 + 2 * ω], by decide⟩
  | 499 => ⟨!![2, 2 * ω; 2, 2 + 2 * ω], by decide⟩
  | 504 => ⟨!![2, 0; 0, 2], by decide⟩
  | 509 => ⟨!![2 + ω, 2 + ω; 2 + 2 * ω, 0], by decide⟩
  | 514 => ⟨!![1 + 2 * ω, 2 * ω; 1, 1], by decide⟩
  | 519 => ⟨!![1, ω; 2, 1 + 2 * ω], by decide⟩
  | 524 => ⟨!![0, 1 + 2 * ω; 1 + ω, 2 + ω], by decide⟩
  | 529 => ⟨!![2 + ω, 1 + 2 * ω; 1 + ω, 0], by decide⟩
  | 533 => ⟨!![2 + 2 * ω, ω; 1, 2], by decide⟩
  | 537 => ⟨!![2 + 2 * ω, 2 * ω; ω, 2 + ω], by decide⟩
  | 541 => ⟨!![2 + ω, 2 + ω; ω, 1 + 2 * ω], by decide⟩
  | 545 => ⟨!![1, 0; 1, 1], by decide⟩
  | 554 => ⟨!![1 + 2 * ω, ω; 2, 1], by decide⟩
  | 557 => ⟨!![2 + 2 * ω, 2; 2, 2 + ω], by decide⟩
  | 560 => ⟨!![ω, 2; ω, 2 + 2 * ω], by decide⟩
  | 568 => ⟨!![2 + 2 * ω, ω; 2 + ω, 2 + 2 * ω], by decide⟩
  | 571 => ⟨!![1 + 2 * ω, 2 + ω; ω, 2 + ω], by decide⟩
  | 579 => ⟨!![1, 2 * ω; 1, 1 + 2 * ω], by decide⟩
  | 581 => ⟨!![2 + ω, 2; 1 + ω, 1 + 2 * ω], by decide⟩
  | 588 => ⟨!![2 + 2 * ω, 2 + 2 * ω; 1, 2 + 2 * ω], by decide⟩
  | 590 => ⟨!![2 + 2 * ω, 2; ω, ω], by decide⟩
  | 597 => ⟨!![2 + ω, 2 * ω; ω, 2 + 2 * ω], by decide⟩
  | 604 => ⟨!![0, 2 + ω; 2 + 2 * ω, 2 + ω], by decide⟩
  | 605 => ⟨!![1, ω; 0, 1], by decide⟩
  | 611 => ⟨!![1 + 2 * ω, 2; 1 + ω, 2 + ω], by decide⟩
  | 617 => ⟨!![2 + ω, 2; 2, 2 + 2 * ω], by decide⟩
  | 623 => ⟨!![2, ω; 1, 2 + 2 * ω], by decide⟩
  | _ => 1

private def exceptionalFn (g : ExceptionalSL5) : ExceptionalSL9 :=
  exceptionalImageTable (exceptionalMatrixKey g)

theorem exceptional_source_word : ∀ g : ExceptionalSL5,
    let code := exceptionalWordCode (exceptionalMatrixKey g)
    evalExceptionalCode exceptionalX5 exceptionalY5 code.1 code.2 = g := by
  set_option maxRecDepth 100000 in
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem exceptional_direct_certificate : ∀ g : ExceptionalSL5,
    exceptionalFn (g * exceptionalX5) = exceptionalFn g * exceptionalX9 ∧
    exceptionalFn (g * exceptionalY5) = exceptionalFn g * exceptionalY9 ∧
    (exceptionalFn g = 1 ↔ g = 1) := by
  decide

theorem exceptionalFn_mul_X (g : ExceptionalSL5) :
    exceptionalFn (g * exceptionalX5) = exceptionalFn g * exceptionalX9 :=
  (exceptional_direct_certificate g).1

theorem exceptionalFn_mul_Y (g : ExceptionalSL5) :
    exceptionalFn (g * exceptionalY5) = exceptionalFn g * exceptionalY9 :=
  (exceptional_direct_certificate g).2.1

theorem exceptionalFn_eq_one_iff (g : ExceptionalSL5) :
    exceptionalFn g = 1 ↔ g = 1 :=
  (exceptional_direct_certificate g).2.2

theorem exceptionalFn_one : exceptionalFn 1 = 1 :=
  (exceptionalFn_eq_one_iff 1).2 rfl

theorem exceptionalFn_mul_eval (a : ExceptionalSL5) : ∀ code n,
    exceptionalFn
        (a * evalExceptionalCode exceptionalX5 exceptionalY5 code n) =
      exceptionalFn a *
        evalExceptionalCode exceptionalX9 exceptionalY9 code n := by
  intro code n
  induction n generalizing a code with
  | zero => simp [evalExceptionalCode]
  | succ n ih =>
      simp only [evalExceptionalCode]
      split
      · rw [← mul_assoc, ih, exceptionalFn_mul_X, mul_assoc]
      · rw [← mul_assoc, ih, exceptionalFn_mul_Y, mul_assoc]

theorem exceptionalFn_eq_eval (g : ExceptionalSL5) :
    exceptionalFn g =
      let code := exceptionalWordCode (exceptionalMatrixKey g)
      evalExceptionalCode exceptionalX9 exceptionalY9 code.1 code.2 := by
  let code := exceptionalWordCode (exceptionalMatrixKey g)
  calc
    exceptionalFn g = exceptionalFn
        (1 * evalExceptionalCode exceptionalX5 exceptionalY5 code.1 code.2) := by
      rw [exceptional_source_word g, one_mul]
    _ = exceptionalFn 1 *
        evalExceptionalCode exceptionalX9 exceptionalY9 code.1 code.2 :=
      exceptionalFn_mul_eval 1 code.1 code.2
    _ = evalExceptionalCode exceptionalX9 exceptionalY9 code.1 code.2 := by
      rw [exceptionalFn_one, one_mul]

theorem exceptionalFn_mul : ∀ a b : ExceptionalSL5,
    exceptionalFn (a * b) = exceptionalFn a * exceptionalFn b := by
  intro a b
  let code := exceptionalWordCode (exceptionalMatrixKey b)
  calc
    exceptionalFn (a * b) = exceptionalFn
        (a * evalExceptionalCode exceptionalX5 exceptionalY5 code.1 code.2) := by
      rw [exceptional_source_word b]
    _ = exceptionalFn a *
        evalExceptionalCode exceptionalX9 exceptionalY9 code.1 code.2 :=
      exceptionalFn_mul_eval a code.1 code.2
    _ = exceptionalFn a * exceptionalFn b := by
      rw [exceptionalFn_eq_eval b]

public def exceptionalHom : ExceptionalSL5 →* ExceptionalSL9 where
  toFun := exceptionalFn
  map_one' := exceptionalFn_one
  map_mul' := exceptionalFn_mul

public theorem exceptionalHom_injective : Function.Injective exceptionalHom := by
  rw [← exceptionalHom.ker_eq_bot_iff]
  ext g
  simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
  exact exceptionalFn_eq_one_iff g

theorem exceptionalHom_X : exceptionalHom exceptionalX5 = exceptionalX9 := by
  have h := exceptionalFn_mul_X (1 : ExceptionalSL5)
  simpa [exceptionalHom, exceptionalFn_one] using h

public theorem exceptionalHom_Y : exceptionalHom exceptionalY5 = exceptionalY9 := by
  have h := exceptionalFn_mul_Y (1 : ExceptionalSL5)
  simpa [exceptionalHom, exceptionalFn_one] using h

theorem evalExceptionalCode_mem_closure {G : Type*} [Group G] (X Y : G)
    (code n : Nat) :
    evalExceptionalCode X Y code n ∈ Subgroup.closure ({X, Y} : Set G) := by
  induction n generalizing code with
  | zero => simp [evalExceptionalCode]
  | succ n ih =>
      rw [evalExceptionalCode]
      apply Subgroup.mul_mem
      · split
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
      · exact ih _

theorem second_word_upper :
    evalExceptionalCode secondRootX9 exceptionalY9 6870 13 =
      Matrix.SpecialLinearGroup.transvection
        (by decide : (0 : Fin 2) ≠ 1) 1 := by
  decide

theorem second_word_lower :
    evalExceptionalCode secondRootX9 exceptionalY9 2412 13 =
      Matrix.SpecialLinearGroup.transvection
        (by decide : (1 : Fin 2) ≠ 0) secondRootF9 := by
  decide

theorem concrete_second_generates :
    Subgroup.closure ({secondRootX9, exceptionalY9} : Set ExceptionalSL9) = ⊤ := by
  let C : Subgroup ExceptionalSL9 :=
    Subgroup.closure ({secondRootX9, exceptionalY9} : Set ExceptionalSL9)
  have hX : secondRootX9 ∈ C := Subgroup.subset_closure (by simp)
  have hY : exceptionalY9 ∈ C := Subgroup.subset_closure (by simp)
  have hXtrans : secondRootX9 =
      Matrix.SpecialLinearGroup.transvection
        (by decide : (0 : Fin 2) ≠ 1) secondRootF9 := by
    decide
  have hYtrans : exceptionalY9 =
      Matrix.SpecialLinearGroup.transvection
        (by decide : (1 : Fin 2) ≠ 0) 1 := by
    decide
  have hUone :
      Matrix.SpecialLinearGroup.transvection
        (by decide : (0 : Fin 2) ≠ 1) 1 ∈ C := by
    rw [← second_word_upper]
    exact evalExceptionalCode_mem_closure secondRootX9 exceptionalY9 6870 13
  have hLr :
      Matrix.SpecialLinearGroup.transvection
        (by decide : (1 : Fin 2) ≠ 0) secondRootF9 ∈ C := by
    rw [← second_word_lower]
    exact evalExceptionalCode_mem_closure secondRootX9 exceptionalY9 2412 13
  have hUr :
      Matrix.SpecialLinearGroup.transvection
        (by decide : (0 : Fin 2) ≠ 1) secondRootF9 ∈ C := by
    simpa [hXtrans] using hX
  have hLone :
      Matrix.SpecialLinearGroup.transvection
        (by decide : (1 : Fin 2) ≠ 0) 1 ∈ C := by
    simpa [hYtrans] using hY
  have hnat {i j : Fin 2} (hij : i ≠ j) (a : ExceptionalF9)
      (ha : Matrix.SpecialLinearGroup.transvection hij a ∈ C) :
      ∀ n : ℕ,
        Matrix.SpecialLinearGroup.transvection hij
          ((n : ExceptionalF9) * a) ∈ C := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Nat.cast_succ, add_mul, one_mul,
          Matrix.SpecialLinearGroup.transvection_add]
        exact C.mul_mem ih ha
  have hdecomp (c : ExceptionalF9) :
      c = algebraMap (ZMod 3) ExceptionalF9 (c.re + c.im) +
        algebraMap (ZMod 3) ExceptionalF9 c.im * secondRootF9 := by
    ext <;> simp [secondRootF9]
  have hupper (c : ExceptionalF9) :
      Matrix.SpecialLinearGroup.transvection
        (by decide : (0 : Fin 2) ≠ 1) c ∈ C := by
    obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (c.re + c.im)
    obtain ⟨m, hm⟩ := ZMod.natCast_zmod_surjective c.im
    rw [hdecomp c, ← hn, ← hm, map_natCast, map_natCast,
      Matrix.SpecialLinearGroup.transvection_add]
    exact C.mul_mem (by simpa using hnat _ 1 hUone n)
      (hnat _ secondRootF9 hUr m)
  have hlower (c : ExceptionalF9) :
      Matrix.SpecialLinearGroup.transvection
        (by decide : (1 : Fin 2) ≠ 0) c ∈ C := by
    obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (c.re + c.im)
    obtain ⟨m, hm⟩ := ZMod.natCast_zmod_surjective c.im
    rw [hdecomp c, ← hn, ← hm, map_natCast, map_natCast,
      Matrix.SpecialLinearGroup.transvection_add]
    exact C.mul_mem (by simpa using hnat _ 1 hLone n)
      (hnat _ secondRootF9 hLr m)
  apply top_unique
  intro A _hA
  apply Matrix.SL2.transvection_induction (fun g => g ∈ C)
  · intro i j hij c
    fin_cases i
    · obtain rfl : j = 1 := by fin_cases j <;> tauto
      exact hupper c
    · obtain rfl : j = 0 := by fin_cases j <;> tauto
      exact hlower c
  · intro A B hA hB
    exact C.mul_mem hA hB

public theorem exceptional_range_eq_closure :
    exceptionalHom.range =
      Subgroup.closure ({exceptionalX9, exceptionalY9} : Set ExceptionalSL9) := by
  apply le_antisymm
  · rintro z ⟨g, rfl⟩
    change exceptionalFn g ∈
      Subgroup.closure ({exceptionalX9, exceptionalY9} : Set ExceptionalSL9)
    rw [exceptionalFn_eq_eval]
    exact evalExceptionalCode_mem_closure exceptionalX9 exceptionalY9
      (exceptionalWordCode (exceptionalMatrixKey g)).1
      (exceptionalWordCode (exceptionalMatrixKey g)).2
  · rw [Subgroup.closure_le]
    intro z hz
    have hz' : z = exceptionalX9 ∨ z = exceptionalY9 := by simpa using hz
    rcases hz' with rfl | rfl
    · exact ⟨exceptionalX5, exceptionalHom_X⟩
    · exact ⟨exceptionalY5, exceptionalHom_Y⟩

theorem concrete_exceptional_equiv :
    Nonempty
      (Subgroup.closure
        ({exceptionalX9, exceptionalY9} : Set ExceptionalSL9) ≃*
          ExceptionalSL5) := by
  let e : ExceptionalSL5 ≃* exceptionalHom.range :=
    MulEquiv.ofBijective exceptionalHom.rangeRestrict
      ⟨by
        intro a b hab
        exact exceptionalHom_injective (congrArg Subtype.val hab),
       MonoidHom.rangeRestrict_surjective exceptionalHom⟩
  exact ⟨(e.trans (MulEquiv.subgroupCongr exceptional_range_eq_closure)).symm⟩

@[expose] public def specialLinearMapEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    Matrix.SpecialLinearGroup (Fin 2) R ≃*
      Matrix.SpecialLinearGroup (Fin 2) S where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by
    apply Subtype.ext
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  right_inv A := by
    apply Subtype.ext
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  map_mul' := map_mul _

/-- If `K` has order nine and `r²+1=0`, the two standard transvections with
parameters `r` and `1` generate a subgroup isomorphic to `SL(2,5)`. -/
public theorem exceptionalF9_two_transvections_equiv_sl2_five
    {K : Type*} [Field K] [Algebra (ZMod 3) K] [Finite K]
    (hKcard : Nat.card K = 9) (r : K) (hr : r ^ 2 + 1 = 0) :
    let XK : Matrix.SpecialLinearGroup (Fin 2) K :=
      ⟨!![1, r; 0, 1], by simp [Matrix.det_fin_two]⟩
    let YK : Matrix.SpecialLinearGroup (Fin 2) K :=
      ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
    Nonempty
      (Subgroup.closure ({XK, YK} : Set _) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  dsimp only
  let liftHom : ExceptionalF9 →ₐ[ZMod 3] K := QuadraticAlgebra.lift ⟨r, by
    have hr' : r * r = -(1 : K) := by
      rw [show r * r = r ^ 2 by ring]
      exact eq_neg_of_add_eq_zero_left hr
    simpa [Algebra.smul_def] using hr'⟩
  let : Fintype K := Fintype.ofFinite K
  have hF9card : Fintype.card ExceptionalF9 = 9 := by
    rw [Fintype.card_congr
      (QuadraticAlgebra.equivProd (-1 : ZMod 3) 0)]
    decide
  have hlift_bij : Function.Bijective liftHom := by
    rw [Fintype.bijective_iff_injective_and_card]
    constructor
    · exact RingHom.injective liftHom.toRingHom
    · rw [hF9card, ← Nat.card_eq_fintype_card]
      exact hKcard.symm
  let e : ExceptionalF9 ≃ₐ[ZMod 3] K :=
    AlgEquiv.ofBijective liftHom hlift_bij
  let E : ExceptionalSL9 ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    specialLinearMapEquiv e.toRingEquiv
  let XK : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![1, r; 0, 1], by simp [Matrix.det_fin_two]⟩
  let YK : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have hEX : E exceptionalX9 = XK := by
    apply Subtype.ext
    ext i j
    change e.toRingHom.mapMatrix (↑exceptionalX9) i j = (↑XK : Matrix (Fin 2) (Fin 2) K) i j
    fin_cases i <;> fin_cases j <;>
      simp [exceptionalX9, XK, e, liftHom]
  have hEY : E exceptionalY9 = YK := by
    apply Subtype.ext
    ext i j
    change e.toRingHom.mapMatrix (↑exceptionalY9) i j = (↑YK : Matrix (Fin 2) (Fin 2) K) i j
    fin_cases i <;> fin_cases j <;>
      simp [exceptionalY9, YK, e, liftHom]
  have hmap :
      (Subgroup.closure
        ({exceptionalX9, exceptionalY9} : Set ExceptionalSL9)).map
          E.toMonoidHom =
        Subgroup.closure ({XK, YK} : Set _) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor <;> aesop
  let eSub :
      Subgroup.closure
          ({exceptionalX9, exceptionalY9} : Set ExceptionalSL9) ≃*
        Subgroup.closure ({XK, YK} : Set _) :=
    (E.subgroupMap
      (Subgroup.closure
        ({exceptionalX9, exceptionalY9} : Set ExceptionalSL9))).trans
      (MulEquiv.subgroupCongr hmap)
  rcases concrete_exceptional_equiv with ⟨e5⟩
  exact ⟨eSub.symm.trans e5⟩

/-- If `K` has order nine and `r²+2r+2=0`, the two standard
transvections with parameters `r` and `1` generate all of `SL(2,K)`. -/
public theorem secondF9_two_transvections_generate
    {K : Type*} [Field K] [Algebra (ZMod 3) K] [Finite K]
    (hKcard : Nat.card K = 9) (r : K)
    (hr : r ^ 2 + 2 * r + 2 = 0) :
    let XK : Matrix.SpecialLinearGroup (Fin 2) K :=
      ⟨!![1, r; 0, 1], by simp [Matrix.det_fin_two]⟩
    let YK : Matrix.SpecialLinearGroup (Fin 2) K :=
      ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
    Subgroup.closure ({XK, YK} : Set _) = ⊤ := by
  dsimp only
  let u : K := r + 1
  have hu : u ^ 2 + 1 = 0 := by
    dsimp [u]
    linear_combination hr
  let liftHom : ExceptionalF9 →ₐ[ZMod 3] K := QuadraticAlgebra.lift ⟨u, by
    have hu' : u * u = -(1 : K) := by
      rw [show u * u = u ^ 2 by ring]
      exact eq_neg_of_add_eq_zero_left hu
    simpa [Algebra.smul_def] using hu'⟩
  let : Fintype K := Fintype.ofFinite K
  have hF9card : Fintype.card ExceptionalF9 = 9 := by
    rw [Fintype.card_congr
      (QuadraticAlgebra.equivProd (-1 : ZMod 3) 0)]
    decide
  have hlift_bij : Function.Bijective liftHom := by
    rw [Fintype.bijective_iff_injective_and_card]
    constructor
    · exact RingHom.injective liftHom.toRingHom
    · rw [hF9card, ← Nat.card_eq_fintype_card]
      exact hKcard.symm
  let e : ExceptionalF9 ≃ₐ[ZMod 3] K :=
    AlgEquiv.ofBijective liftHom hlift_bij
  let E : ExceptionalSL9 ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    specialLinearMapEquiv e.toRingEquiv
  let XK : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![1, r; 0, 1], by simp [Matrix.det_fin_two]⟩
  let YK : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have hEX : E secondRootX9 = XK := by
    apply Subtype.ext
    ext i j
    change e.toRingHom.mapMatrix (↑secondRootX9) i j = (↑XK : Matrix (Fin 2) (Fin 2) K) i j
    fin_cases i <;> fin_cases j <;>
      simp [secondRootX9, XK, secondRootF9,
        e, liftHom, u]
  have hEY : E exceptionalY9 = YK := by
    apply Subtype.ext
    ext i j
    change e.toRingHom.mapMatrix (↑exceptionalY9) i j = (↑YK : Matrix (Fin 2) (Fin 2) K) i j
    fin_cases i <;> fin_cases j <;>
      simp [exceptionalY9, YK, e, liftHom]
  have hmap :
      (Subgroup.closure
        ({secondRootX9, exceptionalY9} : Set ExceptionalSL9)).map
          E.toMonoidHom =
        Subgroup.closure ({XK, YK} : Set _) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor <;> aesop
  rw [concrete_second_generates,
    Subgroup.map_top_of_surjective E.toMonoidHom E.surjective] at hmap
  exact hmap.symm

end Dickson
end CFSG.Glauberman
