module

public import Certificates.Data.W115Rank34

public section

namespace CFSG.KC.F2R34

open CFSG.Quasithin.B45Mat.M22 CFSG.Quasithin.H.Mathieu

@[expose] def xorSel (m r : ℕ) (g : ℕ → ℕ) : ℕ :=
  (List.range m).foldl (fun acc l => bif r.testBit l then acc ^^^ g l else acc) 0

@[expose] def kronRow (a b : ℕ) : ℕ :=
  xorSel 10 a fun l => (b % 2 ^ 10) <<< (10 * l)

@[expose] def xK (tR : List ℕ) (x : ℕ) : ℕ :=
  xorSel 100 x fun i => kronRow (tR.getD (i / 10) 0) (tR.getD (i % 10) 0)

@[expose] def rowF (tR QR : List ℕ) (r : ℕ) : ℕ :=
  xorSel 34 (xorSel 100 (xK tR (xorSel 34 r fun l => P34Rows.getD l 0))
    (fun l => B34Rows.getD l 0) ^^^ r) fun l => QR.getD l 0

@[expose] def colsOK (h : Equiv.Perm (Fin 22)) (cols : List ℕ) : Bool :=
  (List.range 10).all fun j => actC10 (psiArr h) (2 ^ j) == cols.getD j 0

@[expose] def trOK (cols tR : List ℕ) : Bool :=
  (List.range 10).all fun i => (List.range 10).all fun j =>
    (cols.getD j 0).testBit i == (tR.getD i 0).testBit j

@[expose] def check34 (h : Equiv.Perm (Fin 22)) (cols tR PR QR : List ℕ) : Bool :=
  colsOK h cols && trOK cols tR &&
    (List.range 24).all fun i => rowF tR QR (PR.getD i 0) == 2 ^ i

end CFSG.KC.F2R34
