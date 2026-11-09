module

public import Certificates.Data.Kernel.Spor.FiveK
public import Certificates.Data.Kernel.Spor.HKeyU

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def fiveE (n w m : Nat) (G GI : Nat → Nat) (k S : Nat) (r : Nat) :
    Nat → List Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → List Nat → Bool) (fun _ _ => false)
    (fun _ ih L ck => strictB (Nat.land L (nat_lit 7)) (fun l =>
      bIf(Nat.blt l k, strictB (hkeyU n w m (cjK n w m G GI l S)) (fun hy =>
        bIf(Nat.ble (nat_lit 5) (cntD (List.cons hy ck) List.nil), true,
          ih (Nat.shiftRight L (nat_lit 3)) (List.cons hy ck))), false)))
    r

@[expose] noncomputable def fiveTopE (n w m : Nat) (G GI : Nat → Nat) (k r L S : Nat) : Bool :=
  strictB (hkeyU n w m S) (fun hs => fiveE n w m G GI k S r L (List.cons hs List.nil))

end CFSG.KS.MulH

end
