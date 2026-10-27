module

public import Certificates.Data.Kernel.Spor.HexNums

public section

namespace CFSG.KC.HexArrs

open CFSG.KC.Enum CFSG.KS CFSG.KS.HexNums

@[expose] noncomputable def run (d n w N : Nat) (F : Nat → Nat) (cs : List Char) :
    Nat → Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool)
    (fun j _ _ _ _ => Nat.beq j N)
    (fun ch _ ih j e t v acc => bIf(Nat.beq j N, true,
      strictB (hexL (Char.toNat ch)) (fun h => bIf(Nat.blt h (nat_lit 16),
        strictB (Nat.add (Nat.mul v (nat_lit 16)) h) (fun v' =>
        bIf(Nat.beq (Nat.succ t) d,
          bIf(Nat.blt v' (Nat.shiftLeft (nat_lit 1) w),
            strictB (Nat.lor acc (Nat.shiftLeft v' (Nat.mul w e))) (fun acc' =>
              bIf(Nat.beq (Nat.succ e) n,
                bAnd(Nat.beq acc' (F j),
                  ih (Nat.succ j) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)),
                ih j (Nat.succ e) (nat_lit 0) (nat_lit 0) acc')),
            false),
          ih j e (Nat.succ t) v' acc)),
        false))))
    cs

@[expose] noncomputable def hexArrsK (cs : List Char) (d n w N : Nat) (F : Nat → Nat) : Bool :=
  bAnd(Nat.beq cs.length (Nat.mul d (Nat.mul n N)), bAnd(Nat.blt (nat_lit 0) d,
    bAnd(Nat.blt (nat_lit 0) n,
      run d n w N F cs (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0))))

end CFSG.KC.HexArrs

end
