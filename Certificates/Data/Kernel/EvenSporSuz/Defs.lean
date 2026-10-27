module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.SylowCheck
public import CFSG.Certificates.Kernel.Common.StrSplit
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
public import CFSG.Sporadic.Presentation.Common

public section

namespace CFSG.KC.EvenSporSuz

@[expose] def packL : List ℕ → ℕ
  | [] => 0
  | x :: l => x + 64 * packL l

@[expose] def accRow : ℕ → List ℕ → ℕ
  | _, [] => 0
  | r, s :: S => r % 64 * s + accRow (r / 64) S

@[expose] def redGo : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, N => N % 64 % 3 + 64 * redGo n (N / 64)

@[expose] def mulR (R S : List ℕ) : List ℕ := R.map fun r => redGo 12 (accRow r S)

@[expose] def oneR : List ℕ := (List.range 12).map fun i => 64 ^ i

@[expose] def powR (R : List ℕ) : ℕ → List ℕ
  | 0 => oneR
  | n + 1 => mulR (powR R n) R

@[expose] def invR (R : List ℕ) : List ℕ :=
  ((List.range 100).find? fun k => powR R (k + 1) == oneR).elim oneR fun k => powR R k

@[expose] def letterR (M I : List (List ℕ)) (c : ℕ) : List ℕ :=
  if c % 2 = 0 then M.getD (c / 2) oneR else I.getD (c / 2) oneR

@[expose] def evalR (M I : List (List ℕ)) (w : List ℕ) : List ℕ :=
  w.foldl (fun acc c => mulR acc (letterR M I c)) oneR

@[expose] def validR (M I : List (List ℕ)) : Bool :=
  M.length == I.length &&
    (List.range M.length).all fun i =>
      mulR (M.getD i oneR) (I.getD i oneR) == oneR && mulR (I.getD i oneR) (M.getD i oneR) == oneR

@[expose] def rowsOf (A : Array ℕ) : List ℕ :=
  (List.range 12).map fun i => packL ((List.range 12).map fun k => A.getD (12 * i + k) 0)

@[expose] def digitsK (p : List Char) : Bool := !p.isEmpty && p.all Char.isDigit

@[expose] def tokK (p : List Char) : Bool :=
  match p.splitOn ':' with
  | [g, e] => digitsK g && (digitsK e || (e.head? == some '-' && digitsK e.tail))
  | _ => false

@[expose] def natsK (L : List Char) : List ℕ := (L.splitOn ' ').map CFSG.KC.Str.decVal

@[expose] def tokLetters (p : List Char) : List ℕ :=
  match p.splitOn ':' with
  | [g, e] =>
    if e.head? == some '-' then List.replicate (CFSG.KC.Str.decVal e.tail) (2 * CFSG.KC.Str.decVal g + 1)
    else List.replicate (CFSG.KC.Str.decVal e) (2 * CFSG.KC.Str.decVal g)
  | _ => []

@[expose] def lettersK (L : List Char) : List ℕ := (L.splitOn ' ').flatMap tokLetters

@[expose] def linesK (cs : List Char) : List (List Char) := cs.splitOn '\n'

@[expose] def nonEmptyLines (cs : List Char) : List (List Char) :=
  (cs.splitOn '\n').filter fun l => !l.isEmpty

@[expose] def matL (cs : List Char) (k : ℕ) : List ℕ :=
  (((nonEmptyLines cs).drop (12 * k)).take 12).flatMap fun l => l.map fun c => c.toNat - 48

@[expose] def matsK (cs : List Char) : Array (Array ℕ) :=
  ((List.range ((nonEmptyLines cs).length / 12)).map fun k => (matL cs k).toArray).toArray

@[expose] def rowsL (l : List ℕ) : List ℕ :=
  (List.range 12).map fun i => packL ((List.range 12).map fun k => l.getD (12 * i + k) 0)

end CFSG.KC.EvenSporSuz
