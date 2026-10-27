module

public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.ConjRec

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

@[expose] noncomputable def fldO (r o b : Nat) : Nat := fld(r, o, mask b)

@[expose] noncomputable def rdO (rw T i : Nat) : Nat := fldO T (Nat.mul rw i) rw

@[expose] noncomputable def cjO (n w X XI Y YI s e : Nat) : Nat :=
  nIf(Nat.beq s (nat_lit 1), pcomp n w (mask w) Y (pcomp n w (mask w) e YI),
    pcomp n w (mask w) X (pcomp n w (mask w) e XI))

@[expose] noncomputable def okRec (n w cw pb X XI Y YI R T N i r e d : Nat) : Bool :=
  bAnd(bIf(Nat.beq (Nat.succ i) N, true,
      Nat.blt e (fldO (rdO (Nat.add cw (Nat.add pb (nat_lit 6))) T (Nat.succ i)) (nat_lit 0) cw)),
    strictB (fldO r cw pb) fun p => bAnd(Nat.blt p N,
      bIf(Nat.beq d (nat_lit 0), Nat.beq e R,
        strictB (rdO (Nat.add cw (Nat.add pb (nat_lit 6))) T p) fun q =>
          bAnd(Nat.beq (Nat.succ (fldO q (Nat.add cw (Nat.succ pb)) (nat_lit 5))) d,
            Nat.beq e (cjO n w X XI Y YI (fldO r (Nat.add cw pb) (nat_lit 1))
              (fldO q (nat_lit 0) cw))))))

@[expose] noncomputable def okO (n w cw pb X XI Y YI R T N i : Nat) : Bool :=
  strictB (rdO (Nat.add cw (Nat.add pb (nat_lit 6))) T i) fun r =>
    strictB (fldO r (nat_lit 0) cw) fun e =>
      strictB (fldO r (Nat.add cw (Nat.succ pb)) (nat_lit 5)) fun d =>
        okRec n w cw pb X XI Y YI R T N i r e d

end CFSG.KC.ConjRec
