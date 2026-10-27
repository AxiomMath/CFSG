module

public import Certificates.Data.Kernel.B3S3K
public import CFSG.Certificates.Kernel.Lie.CT.Core
public import Mathlib.Data.Nat.Factorial.Basic

public section

namespace CFSG.KC.TcK

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K

@[expose] noncomputable def memK (N : Nat) (T : Nat → Nat) (A : Nat) : Bool :=
  CFSG.KLie.CT.anyN N fun i => Nat.beq A (T i)

@[expose] noncomputable def iv (n w p : Nat) : Nat := pinvS n w (mask w) p

@[expose] noncomputable def tcRestK (n w m X ngQ : Nat) (GQ CU CV : Nat → Nat) (ngK : Nat)
    (GK R : Nat → Nat) (sig : Nat → Nat → Nat) (NQ : Nat) (TQ : Nat → Nat) (NK : Nat)
    (TK : Nat → Nat) (NS : Nat) : Bool :=
  Nat.beq NQ (3 * (m.factorial / 2)) && permB n w X && Nat.beq (pw n w X 3) (pidn n w) &&
    !(Nat.beq X (pidn n w)) &&
    allN ngQ (fun i => permB n w (GQ i) && Nat.beq (cm n w (GQ i) X) (cm n w X (GQ i))) &&
    memK NQ TQ X &&
    Nat.beq (NK * m) NQ && memK NK TK X &&
    allN ngK (fun l => memK NQ TQ (GK l)) &&
    allN m (fun j => permB n w (R j) && memK NQ TQ (R j)) &&
    allN m (fun j => allN m fun k => Nat.beq j k ||
      !(memK NK TK (cm n w (iv n w (R j)) (R k)))) &&
    allN ngQ (fun i => permB n w (CU i) && permB n w (CV i) && memK NQ TQ (CU i) &&
      memK NQ TQ (CV i) &&
      Nat.beq (GQ i) (cm n w (cm n w (CU i) (CV i)) (cm n w (iv n w (CU i)) (iv n w (CV i))))) &&
    allN ngQ (fun i => allN m fun j => Nat.blt (sig i j) m &&
      memK NK TK (cm n w (iv n w (R (sig i j))) (cm n w (GQ i) (R j)))) &&
    Nat.beq NS (m.factorial / 2)

end CFSG.KC.TcK

end
