module

public import CFSG.Certificates.Kernel.Common.StrSplit

public section

namespace CFSG.KC.RouteP

@[expose] def splitPK (c : Char) : List Char → List Char → List (List Char)
  | [], acc => [acc.reverse]
  | a :: t, acc => if a == c then acc.reverse :: splitPK c t [] else splitPK c t (a :: acc)

@[expose] def splitK (c : Char) (l : List Char) : List (List Char) := splitPK c l []

@[expose] def digitsL (ds : List Char) : Bool := !ds.isEmpty && ds.all Char.isDigit

@[expose] def tokInt : List Char → Option Int
  | [] => none
  | '-' :: ds => some (-(CFSG.KC.Str.decVal ds : Int))
  | ds => some (CFSG.KC.Str.decVal ds : Int)

@[expose] def tokIntOK : List Char → Bool
  | [] => true
  | '-' :: ds => digitsL ds
  | ds => digitsL ds

@[expose] def prefLinesL (p cs : List Char) : List (List Int) :=
  ((splitK '\n' cs).filter (p.isPrefixOf ·)).map fun l => ((splitK ' ' l).drop 1).filterMap tokInt

@[expose] def prefOKL (p cs : List Char) : Bool :=
  ((splitK '\n' cs).filter (p.isPrefixOf ·)).all fun l => ((splitK ' ' l).drop 1).all tokIntOK

@[expose] def tokNat (t : List Char) : Option Nat :=
  if t = [] then none else some (CFSG.KC.Str.decVal t)

@[expose] def lineNumsL (p : List Char) (skip : Nat) (cs : List Char) : List Nat :=
  match (splitK '\n' cs).find? (p.isPrefixOf ·) with
  | none => []
  | some l => ((splitK ' ' l).drop skip).filterMap tokNat

@[expose] def lineNumsOKL (p : List Char) (skip : Nat) (cs : List Char) : Bool :=
  match (splitK '\n' cs).find? (p.isPrefixOf ·) with
  | none => true
  | some l => ((splitK ' ' l).drop skip).all fun t => t.isEmpty || digitsL t

@[expose] def tokNatOK (t : List Char) : Bool :=
  match t with
  | [] => true
  | c :: _ => digitsL t || !(c.isDigit || c == '_')

@[expose] def tokNat' (t : List Char) : Option Nat :=
  if digitsL t then some (CFSG.KC.Str.decVal t) else none

@[expose] def levelNumsL (p cs : List Char) : List (List Nat) :=
  ((splitK '\n' cs).filter (p.isPrefixOf ·)).map fun l => (splitK ' ' l).filterMap tokNat'

@[expose] def levelOKL (p cs : List Char) : Bool :=
  ((splitK '\n' cs).filter (p.isPrefixOf ·)).all fun l => (splitK ' ' l).all tokNatOK

end CFSG.KC.RouteP
