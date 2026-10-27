module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public meta import Mathlib.Algebra.QuadraticAlgebra.Defs
public meta import Mathlib.Algebra.Field.ZMod
public meta import Mathlib.Data.ZMod.Defs
public meta import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonExceptionalF9

public section

namespace CFSG

namespace Glauberman
namespace Dickson

open QuadraticAlgebra

instance f9_irreducible :
    Fact (∀ r : ZMod 3, r ^ 2 ≠ (-1 : ZMod 3) + 0 * r) := ⟨by decide⟩

instance : Fintype ExceptionalF9 :=
  Fintype.ofEquiv (ZMod 3 × ZMod 3)
    (QuadraticAlgebra.equivProd (-1 : ZMod 3) 0).symm

@[expose] def secondRootF9 : ExceptionalF9 := ω - 1
@[expose] def secondRootX9 : ExceptionalSL9 :=
  ⟨!![1, secondRootF9; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def exceptionalMatrixKey (g : ExceptionalSL5) : Nat :=
  (g.1 0 0).val + 5 * (g.1 0 1).val +
    25 * (g.1 1 0).val + 125 * (g.1 1 1).val

@[expose] def exceptionalWordCode : Nat → Nat × Nat
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

@[expose] def evalExceptionalCode {G : Type*} [Group G] (X Y : G) : Nat → Nat → G
  | _, 0 => 1
  | code, n + 1 =>
      (if code % 2 = 0 then X else Y) *
        evalExceptionalCode X Y (code / 2) n

@[expose] def exceptionalImage45 : ExceptionalSL9 :=
  ⟨!![0, 2 + ω; 2 + 2 * ω, 0], by decide⟩

@[expose] def exceptionalImage46 : ExceptionalSL9 :=
  ⟨!![2, 0; 1, 2], by decide⟩

@[expose] def exceptionalImage47 : ExceptionalSL9 :=
  ⟨!![2 + ω, 1 + 2 * ω; 2, 2 + ω], by decide⟩

@[expose] def exceptionalImage48 : ExceptionalSL9 :=
  ⟨!![1 + 2 * ω, ω; 1 + ω, 1 + 2 * ω], by decide⟩

@[expose] def exceptionalImage49 : ExceptionalSL9 :=
  ⟨!![1, 2 * ω; 0, 1], by decide⟩

@[expose] def exceptionalImage60 : ExceptionalSL9 :=
  ⟨!![2 * ω, 0; 0, ω], by decide⟩

@[expose] def exceptionalImage61 : ExceptionalSL9 :=
  ⟨!![1 + ω, 2; ω, 2 * ω], by decide⟩

@[expose] def exceptionalImage62 : ExceptionalSL9 :=
  ⟨!![0, 2 + 2 * ω; 2 + ω, 1 + ω], by decide⟩

@[expose] def exceptionalImage63 : ExceptionalSL9 :=
  ⟨!![2 + 2 * ω, 1 + ω; 1 + 2 * ω, 0], by decide⟩

@[expose] def exceptionalImage64 : ExceptionalSL9 :=
  ⟨!![ω, 1; 2 * ω, 2 + 2 * ω], by decide⟩

@[expose] def exceptionalImage90 : ExceptionalSL9 :=
  ⟨!![ω, 0; 0, 2 * ω], by decide⟩

@[expose] def exceptionalImage91 : ExceptionalSL9 :=
  ⟨!![2 * ω, 2; ω, 1 + ω], by decide⟩

@[expose] def exceptionalImage92 : ExceptionalSL9 :=
  ⟨!![1 + ω, 2 + 2 * ω; 2 + ω, 0], by decide⟩

@[expose] def exceptionalImage93 : ExceptionalSL9 :=
  ⟨!![0, 1 + ω; 1 + 2 * ω, 2 + 2 * ω], by decide⟩

@[expose] def exceptionalImage94 : ExceptionalSL9 :=
  ⟨!![2 + 2 * ω, 1; 2 * ω, ω], by decide⟩

@[expose] def exceptionalImage105 : ExceptionalSL9 :=
  ⟨!![0, 1 + 2 * ω; 1 + ω, 0], by decide⟩

@[expose] def exceptionalImage106 : ExceptionalSL9 :=
  ⟨!![2, ω; 0, 2], by decide⟩

@[expose] def exceptionalImage107 : ExceptionalSL9 :=
  ⟨!![2 + ω, 2 * ω; 2 + 2 * ω, 2 + ω], by decide⟩

@[expose] def exceptionalImage108 : ExceptionalSL9 :=
  ⟨!![1 + 2 * ω, 2 + ω; 1, 1 + 2 * ω], by decide⟩

@[expose] def exceptionalImage109 : ExceptionalSL9 :=
  ⟨!![1, 0; 2, 1], by decide⟩

@[expose] def exceptionalImage126 : ExceptionalSL9 :=
  ⟨!![1, 0; 0, 1], by decide⟩

@[expose] def exceptionalImage131 : ExceptionalSL9 :=
  ⟨!![0, 2 + ω; 2 + 2 * ω, 1 + 2 * ω], by decide⟩

@[expose] def exceptionalImage136 : ExceptionalSL9 :=
  ⟨!![2, 2 * ω; 1, 2 + ω], by decide⟩

@[expose] def exceptionalImage141 : ExceptionalSL9 :=
  ⟨!![2 + ω, ω; 2, 2], by decide⟩

@[expose] def exceptionalImage146 : ExceptionalSL9 :=
  ⟨!![1 + 2 * ω, 1 + 2 * ω; 1 + ω, 0], by decide⟩

@[expose] def exceptionalImage151 : ExceptionalSL9 :=
  ⟨!![0, 1 + 2 * ω; 1 + ω, 1 + 2 * ω], by decide⟩

@[expose] def exceptionalImage157 : ExceptionalSL9 :=
  ⟨!![1, 2 * ω; 2, 1 + ω], by decide⟩

@[expose] def exceptionalImage163 : ExceptionalSL9 :=
  ⟨!![1 + 2 * ω, 1; 1, 1 + ω], by decide⟩

@[expose] def exceptionalImage169 : ExceptionalSL9 :=
  ⟨!![2 + ω, 1; 2 + 2 * ω, 1 + 2 * ω], by decide⟩

@[expose] def exceptionalImage170 : ExceptionalSL9 :=
  ⟨!![2, 2 * ω; 0, 2], by decide⟩

@[expose] def exceptionalImage176 : ExceptionalSL9 :=
  ⟨!![2, ω; 2, 2 + ω], by decide⟩

@[expose] def exceptionalImage183 : ExceptionalSL9 :=
  ⟨!![1 + 2 * ω, ω; 2 * ω, 1 + ω], by decide⟩

@[expose] def exceptionalImage185 : ExceptionalSL9 :=
  ⟨!![1 + ω, 1; 2 * ω, 2 * ω], by decide⟩

@[expose] def exceptionalImage192 : ExceptionalSL9 :=
  ⟨!![1 + ω, 1 + ω; 2, 1 + ω], by decide⟩

@[expose] def exceptionalImage199 : ExceptionalSL9 :=
  ⟨!![1 + 2 * ω, 1; 2 + 2 * ω, 2 + ω], by decide⟩

@[expose] def exceptionalImage201 : ExceptionalSL9 :=
  ⟨!![2 + ω, 2 * ω; 1, 2], by decide⟩

@[expose] def exceptionalImage209 : ExceptionalSL9 :=
  ⟨!![2 + ω, 1 + 2 * ω; 2 * ω, 1 + 2 * ω], by decide⟩

@[expose] def exceptionalImage212 : ExceptionalSL9 :=
  ⟨!![1 + ω, 2 * ω; 1 + 2 * ω, 1 + ω], by decide⟩

@[expose] def exceptionalImage215 : ExceptionalSL9 :=
  ⟨!![2 * ω, 1; 2 * ω, 1 + ω], by decide⟩

@[expose] def exceptionalImage223 : ExceptionalSL9 :=
  ⟨!![1 + ω, 1; 1, 1 + 2 * ω], by decide⟩

@[expose] def exceptionalImage226 : ExceptionalSL9 :=
  ⟨!![1 + 2 * ω, 2 + ω; 2 + 2 * ω, 0], by decide⟩

@[expose] def exceptionalImage230 : ExceptionalSL9 :=
  ⟨!![2, 0; 2, 2], by decide⟩

@[expose] def exceptionalImage239 : ExceptionalSL9 :=
  ⟨!![1 + 2 * ω, 1 + 2 * ω; 2 * ω, 2 + ω], by decide⟩

@[expose] def exceptionalImage243 : ExceptionalSL9 :=
  ⟨!![1 + ω, ω; 2 * ω, 1 + 2 * ω], by decide⟩

@[expose] def exceptionalImage247 : ExceptionalSL9 :=
  ⟨!![1 + ω, 2 * ω; 2, 1], by decide⟩

@[expose] def exceptionalImage253 : ExceptionalSL9 :=
  ⟨!![0, 2 + 2 * ω; 2 + ω, 0], by decide⟩

@[expose] def exceptionalImage258 : ExceptionalSL9 :=
  ⟨!![2 + 2 * ω, 2; 1 + 2 * ω, 1 + ω], by decide⟩

@[expose] def exceptionalImage263 : ExceptionalSL9 :=
  ⟨!![ω, 0; 2 * ω, 2 * ω], by decide⟩

@[expose] def exceptionalImage268 : ExceptionalSL9 :=
  ⟨!![2 * ω, 1; 0, ω], by decide⟩

@[expose] def exceptionalImage273 : ExceptionalSL9 :=
  ⟨!![1 + ω, 1 + ω; ω, 2 + 2 * ω], by decide⟩

@[expose] def exceptionalImage278 : ExceptionalSL9 :=
  ⟨!![2 + 2 * ω, 1 + ω; ω, 1 + ω], by decide⟩

@[expose] def exceptionalImage281 : ExceptionalSL9 :=
  ⟨!![1, ω; 1, 1 + ω], by decide⟩

@[expose] def exceptionalImage289 : ExceptionalSL9 :=
  ⟨!![2 + 2 * ω, 1; 1, 2 + ω], by decide⟩

@[expose] def exceptionalImage292 : ExceptionalSL9 :=
  ⟨!![2 + ω, 1; ω, 2 * ω], by decide⟩

@[expose] def exceptionalImage295 : ExceptionalSL9 :=
  ⟨!![2 + ω, ω; 1 + ω, 2 + ω], by decide⟩

@[expose] def exceptionalImage303 : ExceptionalSL9 :=
  ⟨!![ω, 1; 0, 2 * ω], by decide⟩

@[expose] def exceptionalImage309 : ExceptionalSL9 :=
  ⟨!![2 + 2 * ω, ω; 2 * ω, 2 + ω], by decide⟩

@[expose] def exceptionalImage310 : ExceptionalSL9 :=
  ⟨!![0, 1 + ω; 1 + 2 * ω, 1 + ω], by decide⟩

@[expose] def exceptionalImage316 : ExceptionalSL9 :=
  ⟨!![1 + ω, ω; 2 + ω, 1 + ω], by decide⟩

@[expose] def exceptionalImage322 : ExceptionalSL9 :=
  ⟨!![2 * ω, 1; ω, 2 + ω], by decide⟩

@[expose] def exceptionalImage328 : ExceptionalSL9 :=
  ⟨!![2 * ω, 0; 2 * ω, ω], by decide⟩

@[expose] def exceptionalImage332 : ExceptionalSL9 :=
  ⟨!![2 + ω, 2; 2 * ω, 2 * ω], by decide⟩

@[expose] def exceptionalImage336 : ExceptionalSL9 :=
  ⟨!![1 + ω, 2 + 2 * ω; 1, 1 + ω], by decide⟩

@[expose] def exceptionalImage340 : ExceptionalSL9 :=
  ⟨!![1 + ω, 1 + ω; 1 + 2 * ω, 0], by decide⟩

@[expose] def exceptionalImage349 : ExceptionalSL9 :=
  ⟨!![2 + ω, 1; 1, 2 + 2 * ω], by decide⟩

@[expose] def exceptionalImage353 : ExceptionalSL9 :=
  ⟨!![1 + ω, 2; 1 + 2 * ω, 2 + 2 * ω], by decide⟩

@[expose] def exceptionalImage355 : ExceptionalSL9 :=
  ⟨!![2 + ω, 2 + ω; 1, 2 + ω], by decide⟩

@[expose] def exceptionalImage362 : ExceptionalSL9 :=
  ⟨!![2 * ω, 2; 2 * ω, 2 + ω], by decide⟩

@[expose] def exceptionalImage369 : ExceptionalSL9 :=
  ⟨!![2 + ω, ω; 2 * ω, 2 + 2 * ω], by decide⟩

@[expose] def exceptionalImage371 : ExceptionalSL9 :=
  ⟨!![1 + ω, ω; 1, 1], by decide⟩

@[expose] def exceptionalImage377 : ExceptionalSL9 :=
  ⟨!![0, 1 + ω; 1 + 2 * ω, 0], by decide⟩

@[expose] def exceptionalImage382 : ExceptionalSL9 :=
  ⟨!![2 + 2 * ω, 2 + 2 * ω; 2 * ω, 1 + ω], by decide⟩

@[expose] def exceptionalImage387 : ExceptionalSL9 :=
  ⟨!![ω, 2; 0, 2 * ω], by decide⟩

@[expose] def exceptionalImage392 : ExceptionalSL9 :=
  ⟨!![2 * ω, 0; ω, ω], by decide⟩

@[expose] def exceptionalImage397 : ExceptionalSL9 :=
  ⟨!![1 + ω, 1; 2 + ω, 2 + 2 * ω], by decide⟩

@[expose] def exceptionalImage402 : ExceptionalSL9 :=
  ⟨!![2 + 2 * ω, 1; 2 + ω, 1 + ω], by decide⟩

@[expose] def exceptionalImage409 : ExceptionalSL9 :=
  ⟨!![2 + 2 * ω, 2 * ω; 2, 2], by decide⟩

@[expose] def exceptionalImage411 : ExceptionalSL9 :=
  ⟨!![1 + 2 * ω, 2 * ω; ω, 1 + ω], by decide⟩

@[expose] def exceptionalImage418 : ExceptionalSL9 :=
  ⟨!![ω, 1; ω, 1 + 2 * ω], by decide⟩

@[expose] def exceptionalImage420 : ExceptionalSL9 :=
  ⟨!![1 + 2 * ω, 1 + 2 * ω; 2, 1 + 2 * ω], by decide⟩

@[expose] def exceptionalImage427 : ExceptionalSL9 :=
  ⟨!![ω, 0; ω, 2 * ω], by decide⟩

@[expose] def exceptionalImage431 : ExceptionalSL9 :=
  ⟨!![1 + 2 * ω, 2; 2, 1 + ω], by decide⟩

@[expose] def exceptionalImage435 : ExceptionalSL9 :=
  ⟨!![2 + 2 * ω, 2 + 2 * ω; 2 + ω, 0], by decide⟩

@[expose] def exceptionalImage444 : ExceptionalSL9 :=
  ⟨!![2 + 2 * ω, 1 + ω; 2, 2 + 2 * ω], by decide⟩

@[expose] def exceptionalImage448 : ExceptionalSL9 :=
  ⟨!![1 + 2 * ω, 1; ω, ω], by decide⟩

@[expose] def exceptionalImage452 : ExceptionalSL9 :=
  ⟨!![2 * ω, 2; 0, ω], by decide⟩

@[expose] def exceptionalImage458 : ExceptionalSL9 :=
  ⟨!![ω, 2; 2 * ω, 1 + 2 * ω], by decide⟩

@[expose] def exceptionalImage464 : ExceptionalSL9 :=
  ⟨!![2 + 2 * ω, 2 * ω; 1 + 2 * ω, 2 + 2 * ω], by decide⟩

@[expose] def exceptionalImage465 : ExceptionalSL9 :=
  ⟨!![0, 2 + 2 * ω; 2 + ω, 2 + 2 * ω], by decide⟩

@[expose] def exceptionalImage471 : ExceptionalSL9 :=
  ⟨!![1 + ω, 2 * ω; ω, 1 + 2 * ω], by decide⟩

@[expose] def exceptionalImage477 : ExceptionalSL9 :=
  ⟨!![1 + ω, 2 + 2 * ω; 2 * ω, 2 + 2 * ω], by decide⟩

@[expose] def exceptionalImage480 : ExceptionalSL9 :=
  ⟨!![1 + 2 * ω, 2 * ω; 2 + 2 * ω, 1 + 2 * ω], by decide⟩

@[expose] def exceptionalImage488 : ExceptionalSL9 :=
  ⟨!![1 + 2 * ω, 2; 2 * ω, ω], by decide⟩

@[expose] def exceptionalImage491 : ExceptionalSL9 :=
  ⟨!![1 + ω, 2; 2, 1 + 2 * ω], by decide⟩

@[expose] def exceptionalImage499 : ExceptionalSL9 :=
  ⟨!![2, 2 * ω; 2, 2 + 2 * ω], by decide⟩

@[expose] def exceptionalImage504 : ExceptionalSL9 :=
  ⟨!![2, 0; 0, 2], by decide⟩

@[expose] def exceptionalImage509 : ExceptionalSL9 :=
  ⟨!![2 + ω, 2 + ω; 2 + 2 * ω, 0], by decide⟩

@[expose] def exceptionalImage514 : ExceptionalSL9 :=
  ⟨!![1 + 2 * ω, 2 * ω; 1, 1], by decide⟩

@[expose] def exceptionalImage519 : ExceptionalSL9 :=
  ⟨!![1, ω; 2, 1 + 2 * ω], by decide⟩

@[expose] def exceptionalImage524 : ExceptionalSL9 :=
  ⟨!![0, 1 + 2 * ω; 1 + ω, 2 + ω], by decide⟩

@[expose] def exceptionalImage529 : ExceptionalSL9 :=
  ⟨!![2 + ω, 1 + 2 * ω; 1 + ω, 0], by decide⟩

@[expose] def exceptionalImage533 : ExceptionalSL9 :=
  ⟨!![2 + 2 * ω, ω; 1, 2], by decide⟩

@[expose] def exceptionalImage537 : ExceptionalSL9 :=
  ⟨!![2 + 2 * ω, 2 * ω; ω, 2 + ω], by decide⟩

@[expose] def exceptionalImage541 : ExceptionalSL9 :=
  ⟨!![2 + ω, 2 + ω; ω, 1 + 2 * ω], by decide⟩

@[expose] def exceptionalImage545 : ExceptionalSL9 :=
  ⟨!![1, 0; 1, 1], by decide⟩

@[expose] def exceptionalImage554 : ExceptionalSL9 :=
  ⟨!![1 + 2 * ω, ω; 2, 1], by decide⟩

@[expose] def exceptionalImage557 : ExceptionalSL9 :=
  ⟨!![2 + 2 * ω, 2; 2, 2 + ω], by decide⟩

@[expose] def exceptionalImage560 : ExceptionalSL9 :=
  ⟨!![ω, 2; ω, 2 + 2 * ω], by decide⟩

@[expose] def exceptionalImage568 : ExceptionalSL9 :=
  ⟨!![2 + 2 * ω, ω; 2 + ω, 2 + 2 * ω], by decide⟩

@[expose] def exceptionalImage571 : ExceptionalSL9 :=
  ⟨!![1 + 2 * ω, 2 + ω; ω, 2 + ω], by decide⟩

@[expose] def exceptionalImage579 : ExceptionalSL9 :=
  ⟨!![1, 2 * ω; 1, 1 + 2 * ω], by decide⟩

@[expose] def exceptionalImage581 : ExceptionalSL9 :=
  ⟨!![2 + ω, 2; 1 + ω, 1 + 2 * ω], by decide⟩

@[expose] def exceptionalImage588 : ExceptionalSL9 :=
  ⟨!![2 + 2 * ω, 2 + 2 * ω; 1, 2 + 2 * ω], by decide⟩

@[expose] def exceptionalImage590 : ExceptionalSL9 :=
  ⟨!![2 + 2 * ω, 2; ω, ω], by decide⟩

@[expose] def exceptionalImage597 : ExceptionalSL9 :=
  ⟨!![2 + ω, 2 * ω; ω, 2 + 2 * ω], by decide⟩

@[expose] def exceptionalImage604 : ExceptionalSL9 :=
  ⟨!![0, 2 + ω; 2 + 2 * ω, 2 + ω], by decide⟩

@[expose] def exceptionalImage605 : ExceptionalSL9 :=
  ⟨!![1, ω; 0, 1], by decide⟩

@[expose] def exceptionalImage611 : ExceptionalSL9 :=
  ⟨!![1 + 2 * ω, 2; 1 + ω, 2 + ω], by decide⟩

@[expose] def exceptionalImage617 : ExceptionalSL9 :=
  ⟨!![2 + ω, 2; 2, 2 + 2 * ω], by decide⟩

@[expose] def exceptionalImage623 : ExceptionalSL9 :=
  ⟨!![2, ω; 1, 2 + 2 * ω], by decide⟩

@[expose] def exceptionalImageTable : Nat → ExceptionalSL9
  | 45 => exceptionalImage45
  | 46 => exceptionalImage46
  | 47 => exceptionalImage47
  | 48 => exceptionalImage48
  | 49 => exceptionalImage49
  | 60 => exceptionalImage60
  | 61 => exceptionalImage61
  | 62 => exceptionalImage62
  | 63 => exceptionalImage63
  | 64 => exceptionalImage64
  | 90 => exceptionalImage90
  | 91 => exceptionalImage91
  | 92 => exceptionalImage92
  | 93 => exceptionalImage93
  | 94 => exceptionalImage94
  | 105 => exceptionalImage105
  | 106 => exceptionalImage106
  | 107 => exceptionalImage107
  | 108 => exceptionalImage108
  | 109 => exceptionalImage109
  | 126 => exceptionalImage126
  | 131 => exceptionalImage131
  | 136 => exceptionalImage136
  | 141 => exceptionalImage141
  | 146 => exceptionalImage146
  | 151 => exceptionalImage151
  | 157 => exceptionalImage157
  | 163 => exceptionalImage163
  | 169 => exceptionalImage169
  | 170 => exceptionalImage170
  | 176 => exceptionalImage176
  | 183 => exceptionalImage183
  | 185 => exceptionalImage185
  | 192 => exceptionalImage192
  | 199 => exceptionalImage199
  | 201 => exceptionalImage201
  | 209 => exceptionalImage209
  | 212 => exceptionalImage212
  | 215 => exceptionalImage215
  | 223 => exceptionalImage223
  | 226 => exceptionalImage226
  | 230 => exceptionalImage230
  | 239 => exceptionalImage239
  | 243 => exceptionalImage243
  | 247 => exceptionalImage247
  | 253 => exceptionalImage253
  | 258 => exceptionalImage258
  | 263 => exceptionalImage263
  | 268 => exceptionalImage268
  | 273 => exceptionalImage273
  | 278 => exceptionalImage278
  | 281 => exceptionalImage281
  | 289 => exceptionalImage289
  | 292 => exceptionalImage292
  | 295 => exceptionalImage295
  | 303 => exceptionalImage303
  | 309 => exceptionalImage309
  | 310 => exceptionalImage310
  | 316 => exceptionalImage316
  | 322 => exceptionalImage322
  | 328 => exceptionalImage328
  | 332 => exceptionalImage332
  | 336 => exceptionalImage336
  | 340 => exceptionalImage340
  | 349 => exceptionalImage349
  | 353 => exceptionalImage353
  | 355 => exceptionalImage355
  | 362 => exceptionalImage362
  | 369 => exceptionalImage369
  | 371 => exceptionalImage371
  | 377 => exceptionalImage377
  | 382 => exceptionalImage382
  | 387 => exceptionalImage387
  | 392 => exceptionalImage392
  | 397 => exceptionalImage397
  | 402 => exceptionalImage402
  | 409 => exceptionalImage409
  | 411 => exceptionalImage411
  | 418 => exceptionalImage418
  | 420 => exceptionalImage420
  | 427 => exceptionalImage427
  | 431 => exceptionalImage431
  | 435 => exceptionalImage435
  | 444 => exceptionalImage444
  | 448 => exceptionalImage448
  | 452 => exceptionalImage452
  | 458 => exceptionalImage458
  | 464 => exceptionalImage464
  | 465 => exceptionalImage465
  | 471 => exceptionalImage471
  | 477 => exceptionalImage477
  | 480 => exceptionalImage480
  | 488 => exceptionalImage488
  | 491 => exceptionalImage491
  | 499 => exceptionalImage499
  | 504 => exceptionalImage504
  | 509 => exceptionalImage509
  | 514 => exceptionalImage514
  | 519 => exceptionalImage519
  | 524 => exceptionalImage524
  | 529 => exceptionalImage529
  | 533 => exceptionalImage533
  | 537 => exceptionalImage537
  | 541 => exceptionalImage541
  | 545 => exceptionalImage545
  | 554 => exceptionalImage554
  | 557 => exceptionalImage557
  | 560 => exceptionalImage560
  | 568 => exceptionalImage568
  | 571 => exceptionalImage571
  | 579 => exceptionalImage579
  | 581 => exceptionalImage581
  | 588 => exceptionalImage588
  | 590 => exceptionalImage590
  | 597 => exceptionalImage597
  | 604 => exceptionalImage604
  | 605 => exceptionalImage605
  | 611 => exceptionalImage611
  | 617 => exceptionalImage617
  | 623 => exceptionalImage623
  | _ => 1

@[expose] def exceptionalFn (g : ExceptionalSL5) : ExceptionalSL9 :=
  exceptionalImageTable (exceptionalMatrixKey g)

end Dickson

end Glauberman

end CFSG
