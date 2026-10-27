module

public import CFSG.Timmesfeld.Exceptional.DeepQ
public meta import CFSG.Certificates.CosetTableCompactColumns

public section

namespace CFSG.Timmesfeld.Moufang.Deep

open CFSG.Certificates CFSG.CosetTable

@[expose] def letAN (j : ℕ) (b : Bool := true) : Fin 7 × Bool :=
  (⟨j % 7, Nat.mod_lt _ (by decide)⟩, b)

@[expose] def wyAN (i : ℕ) : List (Fin 7 × Bool) := [letAN (i + 2)]

@[expose] def wxAN (i : ℕ) : List (Fin 7 × Bool) := [letAN (i + 2), letAN 1, letAN (i + 2), letAN 1]

@[expose] def repAN (k : ℕ) (w : List (Fin 7 × Bool)) : List (Fin 7 × Bool) :=
  (List.replicate k w).flatten

@[expose] def relsAN : List (List (Fin 7 × Bool)) :=
  [repAN 2 [letAN 0], repAN 2 [letAN 1], repAN 3 [letAN 0, letAN 1]] ++
    (List.range 5).flatMap (fun i => [repAN 2 (wyAN i), [letAN 0] ++ wyAN i ++ [letAN 0] ++ wyAN i,
      repAN 4 (wyAN i ++ [letAN 1]), repAN 3 ([letAN 0] ++ wyAN i ++ [letAN 1]),
      repAN 3 ([letAN 1] ++ wxAN i ++ [letAN 0])]) ++
    (List.range 5).flatMap (fun i => (List.range 5).flatMap (fun j =>
      (if i < j then [repAN 2 (wyAN i ++ wyAN j) ++ [letAN 0 false],
        repAN 2 (wxAN i ++ wxAN j) ++ [letAN 1 false]] else []) ++
      (if i ≠ j then [repAN 3 (wyAN i ++ wxAN j)] else [])))

@[expose] def prodAN : List (Fin 7 × Bool) := (List.range 5).flatMap wyAN

end CFSG.Timmesfeld.Moufang.Deep
