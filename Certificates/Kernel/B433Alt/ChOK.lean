module

public import Certificates.Kernel.B433Alt.Data.St
public import Certificates.Kernel.B433Alt.Data.Ch
public import Certificates.Data.Kernel.B433Alt.Chain

public section

namespace CFSG.KD.B4AC

open CFSG.KC.B4A

@[expose] noncomputable def cbOf (b : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => cbOf b k ||| (b k <<< (15 * k))

@[expose] noncomputable def baseOf (j l : Nat) : Nat := cbOf (fun l' => LB (16 * j + l')) l

@[expose] noncomputable def elChk (e : Nat) : Bool :=
  sB (EL e) fun d => elOK CFSG.KD.B4A.LP CFSG.KD.B4A.RD CFSG.KD.B4A.RW EL EW (baseOf (elJ d) (elL d)) e

@[expose] noncomputable def orbChk (k : Nat) : Bool :=
  sB (CL k) fun kk =>
    Nat.beq (orbRun CFSG.KD.B4A.LP CFSG.KD.B4A.RD CFSG.KD.B4A.RW EL EW (Nat.shiftRight kk 4)
      (Nat.land kk 15) (LG kk) (LN kk) (CN k) (CR k) (CS k)) (CT k)

end CFSG.KD.B4AC

end
