module

public import Certificates.Data.Kernel.MaxD2.Check

public section

namespace CFSG.KS.MaxD2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Row CFSG.KS.PEnum

@[expose] noncomputable def pairK (n w np kw cnt : Nat) (PT T FS KS REP REPI RB2 H2 : Nat → Nat)
    (q i j : Nat) : Bool :=
  strictB (REP j) (fun rp => strictB (REPI i) (fun rpi =>
    bAnd(allN np (fun t => Nat.beq (r32 RB2 (Nat.add (Nat.mul np q) t)) (pg w (mask w) rp (PT t))),
      allN cnt (fun k => strictB (r32 H2 (Nat.add (Nat.mul cnt q) k)) (fun h =>
        bAnd(Nat.beq (Nat.land h (nat_lit 1)) (nat_lit 0),
          testK n w np kw cnt T FS KS rp rpi (fun t => r32 RB2 (Nat.add (Nat.mul np q) t)) k
            h))))))

end CFSG.KS.MaxD2

end
