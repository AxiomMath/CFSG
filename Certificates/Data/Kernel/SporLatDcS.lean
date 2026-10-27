module

public import Certificates.Data.Kernel.SporLatDc

public noncomputable section

namespace CFSG.KC.SLDc

open CFSG.KC.E64F

section Checks

variable (C : DcCtx) (D : DcData) (s : Nat)

@[expose] def orbOKS (j : Nat) : Bool :=
  Nat.blt (D.obase.getD j 0) C.n && Nat.beq (oid D (D.obase.getD j 0)) j &&
    (Nat.beq (D.K.getD j []).length 0 ||
      ((D.K.getD j []).all (fun k => isS C k && Nat.beq (wordF C.L k (D.obase.getD j 0))
        (D.obase.getD j 0)) &&
      sortedLt ((D.K.getD j []).map fun k => D.sep.map (wordF C.L k)) &&
      Nat.beq (Nat.mul (D.K.getD j []).length (D.osz.getD j 0)) s)) &&
    Nat.beq (cntB (fun p => Nat.beq (oid D p) j) (List.range C.n)) (D.osz.getD j 0)

@[expose] def dcCheckS : Bool :=
  globalOK C D && (List.range D.npc).all (ptChunk C D) &&
    (List.range D.obase.length).all (orbOKS C D s) && (List.range D.Rc.length).all (chunkOK C D)

end Checks

end CFSG.KC.SLDc

end
