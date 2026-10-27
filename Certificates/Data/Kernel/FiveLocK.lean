module

public import Certificates.Data.Kernel.K426K

public section

namespace CFSG.KC.FiveLocK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.B3S3K CFSG.KC.K426K CFSG.KC.Misc.ArrEnum

@[expose] noncomputable def commK (n w p q : Nat) : Bool := Nat.beq (cm n w p q) (cm n w q p)

@[expose] noncomputable def lines5K (n w N r : Nat) (T S LX : Nat → Nat) : Bool :=
  allN N (fun k => Nat.beq (pw n w (T k) 5) (pidn n w)) &&
    allN N (fun k => Nat.beq (T k) (pidn n w) ||
      CFSG.KC.LQT.P.anyN r fun j => CFSG.KC.LQT.P.anyN 5 fun e =>
        Nat.beq (T k) (pw n w (LX j) e)) &&
    allN r (fun j => allN r fun j' => Nat.beq j j' ||
      allN 5 fun e => !(Nat.beq (LX j) (pw n w (LX j') e))) &&
    allN r (fun j => permB n w (LX j) && Nat.beq (pw n w (LX j) 5) (pidn n w) &&
      !(Nat.beq (LX j) (pidn n w)) && memIdxK N T S (LX j))

@[expose] noncomputable def transFK (n w r : Nat) (H L : Nat → Nat) (rec : List Nat) : Bool :=
  allN r fun j => permB n w (H j) && Nat.beq (cj n w (H j) (L (rec.getD j 0 % r))) (L j)

@[expose] noncomputable def zPartK (n w N ng X : Nat) (T G : Nat → Nat) : Bool :=
  allN N fun k => !(allN ng fun l => commK n w (T k) (G l)) ||
    CFSG.KC.LQT.P.anyN 5 fun e => Nat.beq (T k) (pw n w X e)

@[expose] noncomputable def selfCentK (n w ngA NC NA : Nat) (GA TC TA SA : Nat → Nat) : Bool :=
  allN ngA (fun l => allN ngA fun l' => commK n w (GA l) (GA l')) &&
    allN NC fun k => !(allN ngA fun l => commK n w (TC k) (GA l)) || memIdxK NA TA SA (TC k)

end CFSG.KC.FiveLocK

end
