module

public import Certificates.Data.Kernel.SmithEK

public section

namespace CFSG.SmithE.K

open CFSG.F4.Native CFSG.SmithE

@[expose] def packD (l : List Nat) : Nat := l.foldr (fun d acc => d + 4 * acc) 0

@[expose] def dig (Q u : Nat) : Nat := (Q >>> (2 * u)) % 4

@[expose] def qd (p u : Nat) : Nat :=
  if u < 36 then f4mul (coord p (u / 6)) (f4mul (coord p (u % 6)) (coord p (u % 6))) else 1

@[expose] def qS (p c : Nat) : Nat := packD ((List.range 37).map fun u => f4mul (qd p u) c)

@[expose] def qOf (p : Nat) : Nat := packD ((List.range 37).map (qd p))

@[expose] def laneQ (Q : Nat) (l : List Nat) : Nat := l.foldl (fun acc u => acc ^^^ dig Q u) 0

@[expose] def termsQ (s t : Nat) : List Nat :=
  let (i0, i1, i2) := tri[s]!
  let (j0, j1, j2) := tri[t]!
  if s = t then [36, 6 * i0 + i0, 6 * i1 + i1, 6 * i2 + i2]
  else
    let inJ := fun i => i == j0 || i == j1 || i == j2
    let inI := fun j => j == i0 || j == i1 || j == i2
    if (inJ i0 && inJ i1) || (inJ i0 && inJ i2) || (inJ i1 && inJ i2) then
      let a := if !inJ i0 then i0 else if !inJ i1 then i1 else i2
      let b := if !inI j0 then j0 else if !inI j1 then j1 else j2
      [6 * a + b]
    else []

@[expose] def cTabQ : List (List (List (List Nat))) :=
  (List.range 20).map fun m => (List.range 10).map fun k => [termsQ k (m / 2), termsQ k (19 - m / 2)]

@[expose] def colQ (QA QB : Nat) (col : List (List (List Nat))) : Nat :=
  col.foldr (fun ab acc => (laneQ QA (ab.getD 0 []) ^^^ laneQ QB (ab.getD 1 [])) + 4 * acc) 0

@[expose] def hQ (T : List (List (List (List Nat)))) (Q Q2 Q3 : Nat) : List Nat :=
  T.zipIdx.map fun cm => if cm.2 % 2 = 0 then colQ Q Q cm.1 else colQ Q2 Q3 cm.1

@[expose] def tvQ (T : List (List (List (List Nat)))) (p : Nat) : List Nat :=
  hQ T (qOf p) (qS p 2) (qS p 3)

end CFSG.SmithE.K
