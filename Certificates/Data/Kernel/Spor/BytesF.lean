module

public import Certificates.Data.Kernel.Spor.Bytes
public import Certificates.Data.Kernel.M1F2

public section

namespace CFSG.KS.Bytes

@[expose] noncomputable def runF (F : Nat → Nat) (lb len : Nat) (cs : List Char) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i len)
    (fun ch _ ih i => (fun c => bAnd(Nat.blt c (nat_lit 128), bAnd(Nat.blt i len,
        bAnd(Nat.beq c (fld(F (Nat.div i lb), Nat.mul (nat_lit 8) (Nat.mod i lb), nat_lit 255)),
          CFSG.KC.M1F2.strictB (Nat.succ i) ih))))
      (Char.toNat ch))
    cs

end CFSG.KS.Bytes

end
