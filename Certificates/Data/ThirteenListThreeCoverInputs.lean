module

public import CFSG.Certificates.CosetTablePresented
public import Mathlib

public section

namespace CFSG.OddTranspositions.PartFour.CoverCard

open CFSG.CosetTable

@[expose] def conjWord (u : List (Fin 6)) (i : Fin 6) : List (Fin 6) := u.reverse ++ i :: u

structure PairRel where
  u : List (Fin 6)
  i : Fin 6
  v : List (Fin 6)
  j : Fin 6
  m : ℕ

@[expose] def PairRel.word (r : PairRel) : List (Fin 6) :=
  (List.replicate r.m (conjWord r.u r.i ++ conjWord r.v r.j)).flatten

@[expose] def coxRels : List PairRel :=
  [⟨[], 0, [], 0, 1⟩, ⟨[], 0, [], 1, 3⟩, ⟨[], 0, [], 2, 2⟩, ⟨[], 0, [], 3, 2⟩, ⟨[], 0, [], 4, 2⟩,
    ⟨[], 0, [], 5, 2⟩, ⟨[], 1, [], 1, 1⟩, ⟨[], 1, [], 2, 3⟩, ⟨[], 1, [], 3, 2⟩, ⟨[], 1, [], 4, 2⟩,
    ⟨[], 1, [], 5, 3⟩, ⟨[], 2, [], 2, 1⟩, ⟨[], 2, [], 3, 3⟩, ⟨[], 2, [], 4, 2⟩, ⟨[], 2, [], 5, 3⟩,
    ⟨[], 3, [], 3, 1⟩, ⟨[], 3, [], 4, 3⟩, ⟨[], 3, [], 5, 2⟩, ⟨[], 4, [], 4, 1⟩, ⟨[], 4, [], 5, 2⟩,
    ⟨[], 5, [], 5, 1⟩]

@[expose] def consRels : List PairRel :=
  [⟨[5, 4], 1, [5], 1, 1⟩, ⟨[4, 5], 3, [4], 3, 1⟩, ⟨[2, 0], 1, [1, 2], 0, 1⟩,
    ⟨[5, 0], 1, [1, 5], 0, 1⟩, ⟨[3, 1], 2, [2, 3], 1, 1⟩, ⟨[4, 2], 3, [3, 4], 2, 1⟩,
    ⟨[3, 5, 3], 2, [5], 2, 1⟩, ⟨[3, 4, 0], 2, [3, 4], 2, 1⟩, ⟨[3, 5, 0], 2, [3, 5], 2, 1⟩,
    ⟨[5, 2, 1], 1, [2, 5], 1, 1⟩]

@[expose] def killConj : List (List (Fin 6) × Fin 6) :=
  [([], 3), ([], 1), ([1, 5], 0), ([1, 5, 2, 1, 3, 2], 0), ([1, 2, 3, 5, 1, 2, 5], 0),
    ([1, 5, 2, 1, 3, 2, 4, 3, 5, 2, 1, 0, 5, 1, 2, 3, 4], 0)]

@[expose] def killWord : List (Fin 6) := (killConj.map fun p => conjWord p.1 p.2).flatten

@[expose] def coverWords : List (List (Fin 6 × Bool)) :=
  ((coxRels ++ consRels).map PairRel.word ++ [killWord]).map (List.map fun x => (x, true))

end CFSG.OddTranspositions.PartFour.CoverCard
