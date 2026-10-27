module

public import Certificates.Data.Kernel.SporLatDc

public noncomputable section

namespace CFSG.KC.SLDc

open CFSG.KC.E64F

section Checks

variable (C : DcCtx) (D : DcData)

@[expose] def ascN : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: l => Nat.blt a b && ascN (b :: l)

@[expose] def orbPts (P : List (List Nat)) (j : Nat) : Bool :=
  ascN (P.getD j []) && (P.getD j []).all (fun p => Nat.blt p C.n && Nat.beq (oid D p) j) &&
    Nat.beq (P.getD j []).length (D.osz.getD j 0)

@[expose] def orbOKL (P : List (List Nat)) (j : Nat) : Bool :=
  Nat.blt (D.obase.getD j 0) C.n && Nat.beq (oid D (D.obase.getD j 0)) j &&
    (Nat.beq (D.K.getD j []).length 0 ||
      ((D.K.getD j []).all (fun k => isS C k && Nat.beq (wordF C.L k (D.obase.getD j 0))
        (D.obase.getD j 0)) &&
      sortedLt ((D.K.getD j []).map fun k => D.sep.map (wordF C.L k)) &&
      Nat.beq (Nat.mul (D.K.getD j []).length (D.osz.getD j 0)) (2 ^ C.k))) &&
    orbPts C D P j

@[expose] def oszOK : Bool :=
  Nat.beq (sumN ((List.range D.obase.length).map fun j => D.osz.getD j 0)) C.n

@[expose] def dcCheckL (P : List (List Nat)) : Bool :=
  globalOK C D && (List.range D.npc).all (ptChunk C D) &&
    (List.range D.obase.length).all (orbOKL C D P) && oszOK C D &&
    (List.range D.Rc.length).all (chunkOK C D)

end Checks

end CFSG.KC.SLDc

end
