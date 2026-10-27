module

public import Certificates.Data.SmithEModel

public section

namespace CFSG.SmithE.K

open CFSG.F4.Native CFSG.SmithE

@[expose] def minorG {α : Type} (zero one : α) (add mul : α → α → α) (x : Nat → α)
    (s t : Nat) : α :=
  let (i0, i1, i2) := tri[s]!
  let (j0, j1, j2) := tri[t]!
  if s = t then
    add (add (add one (mul (x i0) (mul (x i0) (x i0)))) (mul (x i1) (mul (x i1) (x i1))))
      (mul (x i2) (mul (x i2) (x i2)))
  else
    let inJ := fun i => i == j0 || i == j1 || i == j2
    let inI := fun j => j == i0 || j == i1 || j == i2
    if (inJ i0 && inJ i1) || (inJ i0 && inJ i2) || (inJ i1 && inJ i2) then
      let a := if !inJ i0 then i0 else if !inJ i1 then i1 else i2
      let b := if !inI j0 then j0 else if !inI j1 then j1 else j2
      mul (x a) (mul (x b) (x b))
    else zero

@[expose] def minorK (p s t : Nat) : Nat := minorG 0 1 (· ^^^ ·) f4mul (coord p) s t

@[expose] def colK (p m : Nat) : Nat :=
  (List.range 10).foldl (fun acc k =>
    acc + (f4mul (minorK p k (m / 2)) (1 + m % 2) ^^^
      f4mul (minorK p k (19 - m / 2)) (f4sq (1 + m % 2))) * 4 ^ k) 0

@[expose] def tvK (p : Nat) : List Nat := (List.range 20).map (colK p)

end CFSG.SmithE.K
