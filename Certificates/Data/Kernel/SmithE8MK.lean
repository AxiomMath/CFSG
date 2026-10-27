module

public import Certificates.Data.SmithE8MAbel

public section

namespace CFSG.SmithE8M.K

open CFSG.Blueprint.Chevalley

@[expose] def codes : List ℕ := (Tag.rootCertificate .E7).roots

@[expose] def sumRootC (ca cb cm : ℕ) : Bool :=
  (List.range 7).all fun j => ca / 16 ^ j % 16 + cb / 16 ^ j % 16 == cm / 16 ^ j % 16 + 8

@[expose] def rowOf : List (ℕ × ℕ) → ℕ
  | [] => 0
  | p :: r => 2 ^ p.1 ||| rowOf r

@[expose] def eK (rows : List ℕ) (a b : ℕ) : Bool := (rows.getD a 0).testBit b

@[expose] def rowsOK (rows : List ℕ) (edges : List (List (ℕ × ℕ))) : Bool :=
  rows.length == 126 && (List.range 126).all fun a =>
    rows.getD a 0 == rowOf (edges.getD a []) && (edges.getD a []).all fun p =>
      decide (p.1 < 126) && decide (p.2 < 126) &&
        sumRootC (codes.getD a 0) (codes.getD p.1 0) (codes.getD p.2 0)

@[expose] def prs : List ℕ → List (ℕ × ℕ)
  | a :: b :: r => (a, b) :: prs r
  | _ => []

@[expose] def filtK (rw v : ℕ) (P : List ℕ) : List ℕ := P.filter fun u => u != v && !rw.testBit u

@[expose] def coverOK (rows : List ℕ) (P : List ℕ) (k : ℕ) (L : List ℕ) : Bool :=
  decide ((prs L).length < k) && P.all (fun u => (prs L).any fun p => p.1 == u || p.2 == u) &&
    (prs L).all fun p => p.1 == p.2 || eK rows p.1 p.2

@[expose] def abChk (rows : List ℕ) : ℕ → List ℕ → List ℕ → ℕ → Option (List ℕ)
  | 0, _, _, _ => none
  | f + 1, s, P, k =>
    match s with
    | 2 :: r => if P.length < k then some r else none
    | 0 :: n :: r => if coverOK rows P k (r.take (2 * n)) then some (r.drop (2 * n)) else none
    | 1 :: v :: r =>
      match abChk rows f r (P.erase v) k with
      | some r' => abChk rows f r' (filtK (rows.getD v 0) v P) (k - 1)
      | none => none
    | _ => none

@[expose] def chk28 (rows pos t : List ℕ) : Bool := (abChk rows 1000 t pos 28).isSome

@[expose] def chk26 (rows pos nra : List ℕ) (ts : List (List ℕ)) : Bool :=
  nra.length == ts.length && (nra.zip ts).all fun p =>
    (abChk rows 1000 p.2 (filtK (rows.getD p.1 0) p.1 pos) 26).isSome

end CFSG.SmithE8M.K
