module

public import CFSG.Sporadic.Schreier.CountSpec
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public meta import CFSG.Sporadic.Schreier.CountSpec
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace Certificates.Odd87F3

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier CFSG.Certificates

structure Row where
  prime : ℕ
  pexp : ℕ
  oddExp : ℕ
  oddWords : List (List ℤ)

@[expose] def witnessOK (n e : ℕ) (WT : List (Table × Table)) (x : Table) : Bool :=
  WT.any (fun w => !powFixW n [x, w.1, x, w.2] e) ||
    WT.any fun w₁ => WT.any fun w₂ => !powFixW n [x, w₁.1, x, w₁.2, w₂.1, x, w₂.2] e

@[expose] def candAllT (n : ℕ) (Tss : List (List Table)) (uT : Table) : List Table :=
  filterProducts n (fun T => let ux := compT n uT T; tblEq n (compT n ux ux) (idT n)) Tss (idT n) []

@[expose] def candAll (n : ℕ) (Q : RawSchreierDatum n) (uT : Table) : List Table :=
  candAllT n (levelTables Q) uT

@[expose] def rowOK (n : ℕ) (Q : RawSchreierDatum n) (gG : List (Equiv.Perm (Fin n)))
    (u : Equiv.Perm (Fin n)) (cands : List Table) (r : Row) : Bool :=
  let uT := toTable u
  let og := r.oddWords.map (evalCodes gG)
  tblEq n (compT n uT uT) (idT n) && (r.oddExp % 2 == 1) &&
    (Q.orderCertificate % r.prime ^ (r.pexp + 1) != 0) &&
    og.all (fun g => commT n uT (toTable g) && powFixW n [toTable g] r.oddExp) &&
    cands.all fun T => !ordTest n r.prime T ||
      witnessOK n (r.prime ^ r.pexp) (og.map fun g => (toTable g, toTable g⁻¹)) T

@[expose] def evalT (n : ℕ) (gT gIT : List Table) : List ℤ → Table
  | [] => idT n
  | z :: w =>
    compT n (if 0 < z then gT.getD (z.toNat - 1) (idT n) else gIT.getD ((-z).toNat - 1) (idT n))
      (evalT n gT gIT w)

@[expose] def rowOKT (n NG : ℕ) (gT : List Table) (uT : Table) (cands : List Table) (r : Row) : Bool :=
  let gIT := gT.map (invT n)
  let og := r.oddWords.map (evalT n gT gIT)
  tblEq n (compT n uT uT) (idT n) && (r.oddExp % 2 == 1) &&
    (NG % r.prime ^ (r.pexp + 1) != 0) &&
    gT.all (fun g => invOK n g (invT n g) && commT n uT g) &&
    og.all (fun g => invOK n g (invT n g) && powFixW n [g] r.oddExp) &&
    cands.all fun T => !ordTest n r.prime T ||
      witnessOK n (r.prime ^ r.pexp) (og.map fun g => (g, invT n g)) T

@[expose] def rowsOKT (n NG : ℕ) (Tss : List (List Table)) (gT : List Table) (uT : Table)
    (rs : List Row) : Bool :=
  let cands := candAllT n Tss uT
  rs.all (rowOKT n NG gT uT cands)

@[expose] def rowsOK (n : ℕ) (Q : RawSchreierDatum n) (gG : List (Equiv.Perm (Fin n)))
    (u : Equiv.Perm (Fin n)) (rs : List Row) : Bool :=
  let cands := candAll n Q (toTable u)
  rs.all (rowOK n Q gG u cands)

@[expose] def coverOK (n : ℕ) (Q : RawSchreierDatum n) (a b g₀ : Equiv.Perm (Fin n))
    (reps : List (Equiv.Perm (Fin n))) (cap : ℕ) : Bool :=
  repsOK n (pairTables a b) (pairTables a⁻¹ b⁻¹) (cosetOrderTables Q g₀ 2) (reps.map toTable) cap &&
    reps.all fun r => ordTest n 2 (toTable r)

end Certificates.Odd87F3
