module

public import Certificates.Data.J2C4725

public section

namespace CFSG.RankThree.PartTwo.J2Residue.H2S

open CFSG.ComponentClassification.J2Cover.Models CFSG.Monster.B.Co2.Native
open CFSG.RankThree.PartTwo.J2Residue.C4725
open CFSG.Sporadic.Fi23.Native (natsOf)

@[expose] def h2Free : List Nat := [
  84, 85, 86, 87, 89, 95, 108, 109, 110, 111, 113, 119, 228, 229, 230, 231, 384, 385, 386, 389,
  444, 445, 446, 449, 840, 841, 1368, 1369, 1560, 1561]

@[expose] def idCols : List Nat := (List.range 12).map (2 ^ ·)

@[expose] def mulColsMat (P Q : List Nat) : List Nat :=
  (List.range 12).map fun c => mulCols P (Q.getD c 0)

@[expose] def matWord (w : List Nat) : List Nat :=
  w.foldl (fun acc j => mulColsMat acc (colsJ j)) idCols

@[expose] def invColsJ (j : Nat) : List Nat := if j = 0 then aCols else mulColsMat bCols bCols

@[expose] def matWordInv (w : List Nat) : List Nat :=
  w.foldl (fun acc j => mulColsMat (invColsJ j) acc) idCols

@[expose] def yCols (k : Nat) : List Nat := matWord (nth [] yWords k)

end CFSG.RankThree.PartTwo.J2Residue.H2S
