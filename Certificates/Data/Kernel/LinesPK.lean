module

public import Certificates.Data.Kernel.FiveLocK

public section

namespace CFSG.KC.LinesPK

open CFSG.KC.Enum CFSG.KS CFSG.KC.B3S3K CFSG.KC.K426K CFSG.KC.Misc.ArrEnum

@[expose] noncomputable def linesPK (n w p N r : Nat) (T S LX : Nat → Nat) : Bool :=
  allN N (fun k => Nat.beq (pw n w (T k) p) (pidn n w)) &&
    allN N (fun k => Nat.beq (T k) (pidn n w) ||
      CFSG.KC.LQT.P.anyN r fun j => CFSG.KC.LQT.P.anyN p fun e =>
        Nat.beq (T k) (pw n w (LX j) e)) &&
    allN r (fun j => allN r fun j' => Nat.beq j j' ||
      allN p fun e => !(Nat.beq (LX j) (pw n w (LX j') e))) &&
    allN r (fun j => permB n w (LX j) && Nat.beq (pw n w (LX j) p) (pidn n w) &&
      !(Nat.beq (LX j) (pidn n w)) && memIdxK N T S (LX j))

end CFSG.KC.LinesPK

end
