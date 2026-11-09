module

public import Certificates.Data.Kernel.Spor.RawSch3G

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def stwK (n w m idn : Nat) (S SI : Nat → Nat) (kS T TJ : Nat)
    (W : List (List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun j => Nat.beq j (Nat.shiftRight (stCnt T) (nat_lit 1)))
    (fun wd _ ih j => bAnd(wlK kS TJ wd,
      bAnd(Nat.beq (letterK S SI kS (stAt T j)) (wvK n w m idn S SI kS TJ wd),
        ih (Nat.succ j)))) W

end CFSG.KS.Raw

end
