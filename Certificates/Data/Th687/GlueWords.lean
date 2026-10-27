module

public import CFSG.Certificates.WordSubgroup
public import CFSG.Sporadic.Recognition.PresentedWordsClosure
import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Certificates.CosetTableShort
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.ThInputs
public import Mathlib

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.CosetTable
open CFSG.Sporadic.Recognition.PresentedWords

inductive Twist where
  | id
  | f1
  | f3
  | f13
  deriving DecidableEq

instance : Fintype Twist :=
  ⟨{.id, .f1, .f3, .f13}, by intro x; cases x <;> simp⟩

abbrev Config := Twist × Fin 2

@[expose] def R0' : List (List (Fin 8 × Bool)) :=
  (TauCeti.Sporadic.Thompson.presentation.relators : List (List (Fin 8 × Bool)))

@[expose] def wY : Twist → Fin 6 → List (Fin 8 × Bool)
  | .id, 0 => [(0, false)]
  | .id, 1 => [(2, false)]
  | .id, 2 => [(3, false)]
  | .id, 3 => [(4, false)]
  | .id, 4 => [(7, true)]
  | .id, 5 => [(6, true)]
  | .f1, 0 => [(0, false)]
  | .f1, 1 => [(2, false)]
  | .f1, 2 => [(3, false)]
  | .f1, 3 => [(4, false)]
  | .f1, 4 => [(6, true), (7, false), (0, false)]
  | .f1, 5 => [(6, true)]
  | .f3, 0 => [(0, false)]
  | .f3, 1 => [(2, false)]
  | .f3, 2 => [(3, false)]
  | .f3, 3 => [(4, false)]
  | .f3, 4 => [(0, true), (7, true)]
  | .f3, 5 => [(6, true)]
  | .f13, 0 => [(0, false)]
  | .f13, 1 => [(2, false)]
  | .f13, 2 => [(3, false)]
  | .f13, 3 => [(4, false)]
  | .f13, 4 => [(6, true), (7, false)]
  | .f13, 5 => [(6, true)]

@[expose] def xw : Config → Fin 2 → List (Fin 8 × Bool)
  | (.id, 0), 0 =>
    [(2, false), (3, false), (2, false), (3, false), (0, false), (1, true), (0, true), (2, true),
     (1, true), (3, true), (2, true), (3, true), (1, false)]
  | (.id, 0), 1 => [(2, false), (3, false), (2, false), (3, false), (1, true), (2, true)]
  | (.id, 1), 0 =>
    [(2, false), (4, false), (3, false), (2, false), (1, true), (2, true), (3, true), (4, true)]
  | (.id, 1), 1 =>
    [(3, false), (4, false), (3, false), (2, false), (3, false), (2, false), (1, false), (2, true),
     (3, true), (2, true), (3, true), (4, true), (3, true), (2, true)]
  | (.f1, 0), 0 =>
    [(2, false), (0, true), (3, true), (4, true), (1, true), (0, true), (2, true), (1, true),
     (4, true), (3, true)]
  | (.f1, 0), 1 =>
    [(2, false), (3, false), (2, false), (3, false), (1, false), (2, false), (3, false), (2, false),
     (3, false), (1, false), (0, false)]
  | (.f1, 1), 0 =>
    [(2, false), (3, false), (2, false), (3, false), (4, false), (3, false), (2, false), (0, false),
     (1, true), (2, true), (3, true), (2, true), (4, true)]
  | (.f1, 1), 1 =>
    [(2, false), (1, true), (7, true), (3, false), (2, false), (3, false), (7, false), (3, false),
     (1, false)]
  | (.f3, 0), 0 =>
    [(3, false), (2, false), (3, false), (2, false), (1, false), (3, true), (2, true), (3, true)]
  | (.f3, 0), 1 =>
    [(2, false), (1, true), (2, true), (3, true), (2, true), (1, true), (3, true), (2, true),
     (0, false)]
  | (.f3, 1), 0 =>
    [(7, false), (4, false), (3, false), (2, false), (3, false), (7, false), (3, false), (1, true),
     (3, false), (2, false), (3, false), (0, false), (1, false), (2, false), (3, false)]
  | (.f3, 1), 1 =>
    [(2, false), (3, false), (2, false), (3, false), (1, true), (3, true), (7, true), (3, true),
     (2, true), (3, true), (7, false), (1, false)]
  | (.f13, 0), 0 =>
    [(2, false), (3, false), (2, false), (3, false), (3, false), (1, false), (2, false), (3, false),
     (0, false)]
  | (.f13, 0), 1 =>
    [(3, false), (4, false), (2, false), (1, true), (0, true), (2, true), (1, true), (4, true),
     (3, true), (2, true)]
  | (.f13, 1), 0 =>
    [(1, true), (2, true), (3, true), (4, true), (3, true), (2, true), (1, true), (7, false),
     (4, false), (3, false), (2, false), (3, false), (7, true), (3, false)]
  | (.f13, 1), 1 =>
    [(2, false), (7, true), (3, true), (2, true), (3, true), (7, true), (1, false), (7, true),
     (3, false), (2, false), (3, false), (7, false), (1, false), (3, false), (4, false)]

@[expose] def bfree : List (List (Fin 8 × Bool)) :=
  R0'.filter fun w => w.all fun l => l.1 ≠ 1

@[expose] def brel : List (List (Fin 8 × Bool)) :=
  R0'.filter fun w => w.any (fun l => l.1 = 1) && w.all fun l => l.1 ≠ 5

@[expose] def hsK (k : Twist) : List (List (Fin 8 × Bool)) :=
  [wY k 0, [(1, true)], wY k 1, wY k 2, wY k 3, [(5, true)], wY k 5, wY k 4]

@[expose] def collapseRels (c : Config) : List (List (Fin 8 × Bool)) :=
  bfree ++ brel.map (substWord (hsK c.1)) ++
    (List.ofFn (xw c)).map fun w => commWord [(5, true)] (substWord (hsK c.1) w)

end CFSG.Sporadic.Th.Recog
