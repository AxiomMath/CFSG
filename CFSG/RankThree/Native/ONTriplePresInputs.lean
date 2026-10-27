module

public import CFSG.Certificates.CosetTableCompactColumns
public meta import CFSG.Certificates.CosetTableCompactColumns
public meta import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.CosetTableShort
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.RankThree.Native.ONTriple

open CFSG.CosetTable

@[expose] def zInv (e : ℕ) : List (Fin 8 × Bool) := List.replicate e (7, false)

@[expose] def coverRels (e₁ e₂ e₃ : ℕ) : List (List (Fin 8 × Bool)) := [
    [(0, true), (0, true)],
    [(1, true), (1, true)],
    [(2, true), (2, true)],
    [(3, true), (3, true)],
    [(4, true), (4, true)],
    [(5, true), (5, true)],
    [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true)],
    [(1, true), (2, true), (1, true), (2, true), (1, true), (2, true)],
    [(2, true), (3, true), (2, true), (3, true), (2, true), (3, true), (2, true),
      (3, true), (2, true), (3, true), (2, true), (3, true), (2, true), (3, true),
      (2, true), (3, true)],
    [(3, true), (4, true), (3, true), (4, true), (3, true), (4, true)],
    [(4, true), (5, true), (4, true), (5, true), (4, true), (5, true)],
    [(0, true), (2, true), (0, true), (2, true)],
    [(0, true), (3, true), (0, true), (3, true)],
    [(0, true), (4, true), (0, true), (4, true)],
    [(0, true), (5, true), (0, true), (5, true)],
    [(1, true), (3, true), (1, true), (3, true)],
    [(1, true), (4, true), (1, true), (4, true)],
    [(1, true), (5, true), (1, true), (5, true)],
    [(2, true), (4, true), (2, true), (4, true)],
    [(2, true), (5, true), (2, true), (5, true)],
    [(3, true), (5, true), (3, true), (5, true)],
    [(6, true), (6, true), (6, true), (6, true)],
    [(5, false), (0, false), (6, true), (6, true)],
    [(5, false), (0, false), (2, true), (3, true), (2, true), (3, true), (2, true),
      (3, true), (2, true), (3, true)],
    [(2, true), (6, false), (3, false), (6, false), (3, false), (2, true), (3, true),
      (6, true), (3, true), (6, true)],
    [(3, true), (6, false), (2, false), (6, false), (2, false), (3, true), (2, true),
      (6, true), (2, true), (6, true)],
    [(1, true), (2, true), (3, true), (6, true), (1, true), (2, true), (3, true),
      (6, true), (1, true), (2, true), (3, true), (6, true), (1, true), (2, true),
      (3, true), (6, true), (1, true), (2, true), (3, true), (6, true)] ++ zInv e₁,
    [(6, true), (1, true), (2, false), (6, true), (2, true), (1, false), (6, true),
      (1, true), (2, false), (6, true), (2, true)] ++ zInv e₂,
    [(6, true), (4, true), (3, false), (6, true), (3, true), (4, false), (6, true),
      (4, true), (3, false), (6, true), (3, true)] ++ zInv e₃,
    [(7, true), (7, true), (7, true)],
    [(7, true), (0, true), (7, false), (0, false)],
    [(7, true), (1, true), (7, false), (1, false)],
    [(7, true), (2, true), (7, false), (2, false)],
    [(7, true), (3, true), (7, false), (3, false)],
    [(7, true), (4, true), (7, false), (4, false)],
    [(7, true), (5, true), (7, false), (5, false)],
    [(7, true), (6, true), (7, false), (6, false)]]

abbrev C1 := restrictWords (subsetOf 8 [0, 1, 2, 3, 4, 5]) (coverRels 1 1 1)

abbrev C2 := restrictWords (subsetOf _ [0, 2, 3, 4, 5]) C1

abbrev C3 := restrictWords (subsetOf _ [0, 2, 3, 4]) C2

abbrev C4 := restrictWords (subsetOf _ [1, 2, 3]) C3

abbrev C5 := restrictWords (subsetOf _ [1, 2]) C4

abbrev C6 := restrictWords (subsetOf _ [1]) C5

end CFSG.RankThree.Native.ONTriple
