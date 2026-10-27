module

public import CFSG.Sporadic.Schreier.CountSpec
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public meta import CFSG.Sporadic.Schreier.CountSpec
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace Certificates.CF67

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier CFSG.Certificates

@[expose] def cf67PowT (n : ℕ) (T : Table) : ℕ → Table
  | 0 => idT n
  | k + 1 => compT n T (cf67PowT n T k)

@[expose] def commAllT (n : ℕ) (Tss : List (List Table)) (aT bT : Table) : List Table :=
  filterProducts n (fun T => commT n aT T && commT n bT T) Tss (idT n) []

@[expose] def cf67OKT (n NG : ℕ) (Tss : List (List Table)) (aT bT : Table) (r : ℕ) : Bool :=
  powFixW n [aT] r && powFixW n [bT] r && commT n aT bT && !tblEq n aT (idT n) &&
    (List.range r).all (fun i => !tblEq n bT (cf67PowT n aT i)) && (NG % r ^ 3 != 0) &&
    (commAllT n Tss aT bT).all fun T => powFixW n [T] (r ^ 2)

@[expose] def cf67OK (n : ℕ) (Q : RawSchreierDatum n) (gG : List (Equiv.Perm (Fin n))) (r : ℕ)
    (wa wb : List ℤ) : Bool :=
  cf67OKT n Q.orderCertificate (levelTables Q) (toTable (evalCodes gG wa))
    (toTable (evalCodes gG wb)) r

@[expose] def cf67Gen (n r : ℕ) (a b : Table) : List Table :=
  (List.range r).flatMap fun i => (List.range r).map fun j => compT n (cf67PowT n a i)
    (cf67PowT n b j)

@[expose] def cf67IsPair (n r : ℕ) (a b : Table) : Bool :=
  powFixW n [a] r && powFixW n [b] r && !tblEq n a (idT n) &&
    (List.range r).all (fun i => !tblEq n b (cf67PowT n a i)) && commT n a b

@[expose] def cf67CoverT (n r : ℕ) (PT : List Table) (Es : List (Table × Table)) : Bool :=
  PT.all fun a => PT.all fun b =>
    !cf67IsPair n r a b ||
      Es.any fun e => (cf67Gen n r a b).any (tblEq n e.1) && (cf67Gen n r a b).any (tblEq n e.2)

@[expose] def cf67ClosedT (n : ℕ) (PT : List Table) : Bool :=
  PT.any (tblEq n (idT n)) && PT.all (fun a => PT.any fun b => tblEq n (compT n a b) (idT n)) &&
    PT.all fun a => PT.all fun b => PT.any (tblEq n (compT n a b))

@[expose] def cf67NodupT (n : ℕ) : List Table → Bool
  | [] => true
  | a :: l => l.all (fun b => !tblEq n a b) && cf67NodupT n l

@[expose] def cf67GenOKT (n NG r k t : ℕ) (Tss : List (List Table)) (PT : List Table)
    (Es : List (Table × Table)) : Bool :=
  (PT.length == r ^ k) && cf67NodupT n PT && cf67ClosedT n PT && (NG % r ^ (k + 1) != 0) &&
    cf67CoverT n r PT Es &&
    Es.all fun e => (commAllT n Tss e.1 e.2).all fun T => powFixW n [T] (2 ^ t * r ^ k)

@[expose] def cf67GenOK (n : ℕ) (Q : RawSchreierDatum n) (gG : List (Equiv.Perm (Fin n)))
  (r k t : ℕ)
    (Pw : List (List ℤ)) (Ew : List (List ℤ × List ℤ)) : Bool :=
  cf67GenOKT n Q.orderCertificate r k t (levelTables Q) (Pw.map fun w => toTable (evalCodes gG w))
    (Ew.map fun e => (toTable (evalCodes gG e.1), toTable (evalCodes gG e.2)))

end Certificates.CF67
