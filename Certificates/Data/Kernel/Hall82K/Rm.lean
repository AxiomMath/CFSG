module

public import Certificates.Data.Kernel.Hall82K.Enum
public import Certificates.Data.Kernel.Hall82K.PermK

public section

namespace CFSG.KC.Hall82K

open CFSG.KC.Ord CFSG.KC.LQT

@[expose] noncomputable def negK (b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false b

@[expose] noncomputable def powL (c n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idK (fun _ ih => compL ih c) n

@[expose] def u0MaskK : Nat := 3425946675

@[expose] def inUK (v : Nat) : Bool := Nat.beq (bitN u0MaskK v) 1

@[expose] def fix5K (c : Nat) : Bool := Nat.beq (apL c 5) 5

@[expose] def rmC (R e : Nat) : Nat := lane R 36 68719476735 e

@[expose] def inM (m e : Nat) : Bool := Nat.beq (bitN m e) 1

@[expose] noncomputable def rmBasicK (R : Nat) : Bool :=
  andB (Nat.beq (rmC R 0) idK)
    (P.allN 8 fun e => andB (permK (rmC R e)) (andB (fix5K (rmC R e))
      (P.allN 8 fun f => andB (Nat.beq (compL (rmC R e) (rmC R f)) (rmC R (Nat.xor e f)))
        (P.impB (Nat.beq (rmC R e) (rmC R f)) (Nat.beq e f)))))

@[expose] noncomputable def rmMemK (E : Nat → Nat) (I R : Nat) : Bool :=
  P.allN 8 fun e => P.letB (lane I 12 4095 e) fun k => andB (Nat.blt k 2160) (Nat.beq (E k) (rmC R e))

@[expose] noncomputable def rmNotLeK (EL : Nat → Nat) (R : Nat) : Bool :=
  P.allN 1080 fun k => negK (Nat.beq (EL k) (rmC R 2))

@[expose] noncomputable def nvWitK (EL : Nat → Nat) (x r : Nat) : Bool :=
  P.letB (Nat.land r 2047) fun w => P.letB (Nat.shiftRight r 11) fun wi =>
    andB (Nat.blt w 1080) (andB (Nat.blt wi 1080) (andB (fix5K (EL w))
      (andB (Nat.beq (compL (EL w) (EL wi)) idK)
        (negK (Nat.beq (powL (compL x (powL (compL (compL (EL w) x) (EL wi)) 15)) 16) idK)))))

@[expose] noncomputable def nvAtK (E EL : Nat → Nat) (R W k : Nat) : Bool :=
  P.letB (E k) fun x =>
    P.impB (andB (fix5K x) (andB (negK (Nat.beq x idK)) (Nat.beq (powL x 16) idK)))
      (orB (P.anyN 8 fun e => Nat.beq x (rmC R e)) (nvWitK EL x (lane W 22 4194303 k)))

@[expose] noncomputable def closed8K (m : Nat) : Bool :=
  P.allN 8 fun e => P.allN 8 fun f => P.impB (andB (inM m e) (inM m f)) (inM m (Nat.xor e f))

@[expose] noncomputable def quadK (R m : Nat) : Bool :=
  P.allN 8 fun e => P.allN 8 fun f => P.impB (andB (inM m e) (inM m f))
    (P.allN 64 fun v => Nat.beq (Nat.xor (Nat.xor (apL (rmC R e) (apL (rmC R f) v))
      (apL (rmC R e) v)) (Nat.xor (apL (rmC R f) v) v)) 0)

@[expose] noncomputable def subWitK (EL : Nat → Nat) (R m r : Nat) : Bool :=
  P.letB (Nat.land r 2047) fun w => P.letB (Nat.land (Nat.shiftRight r 11) 2047) fun wi =>
    P.letB (Nat.land (Nat.shiftRight r 22) 7) fun e => P.letB (Nat.shiftRight r 25) fun f =>
      andB (Nat.blt w 1080) (andB (Nat.blt wi 1080) (andB (fix5K (EL w))
        (andB (Nat.beq (compL (EL w) (EL wi)) idK) (andB (inM m e) (andB (Nat.blt f 8)
          (andB (negK (inM m f))
            (Nat.beq (compL (compL (EL w) (rmC R e)) (EL wi)) (rmC R f))))))))

@[expose] noncomputable def subsetAtK (EL : Nat → Nat) (R S m : Nat) : Bool :=
  P.impB (closed8K m)
    (orB (Nat.beq m 255) (orB (quadK R m) (subWitK EL R m (lane S 32 4294967295 m))))

@[expose] noncomputable def uInvAtK (E : Nat → Nat) (k : Nat) : Bool :=
  P.letB (E k) fun x => P.impB (fix5K x) (P.allN 64 fun u => P.impB (inUK u) (inUK (apL x u)))

@[expose] noncomputable def rmUK (R : Nat) : Bool :=
  P.allN 8 fun e => andB
    (P.allN 64 fun u => P.impB (inUK u) (P.letB (Nat.xor (apL (rmC R e) u) u) fun d =>
      orB (Nat.beq d 0) (Nat.beq d 5)))
    (orB (Nat.beq e 0) (P.anyN 64 fun u => andB (inUK u) (negK (Nat.beq (apL (rmC R e) u) u))))

@[expose] noncomputable def fixRmK (R : Nat) : Bool :=
  P.allN 64 fun v => orB (orB (Nat.beq v 0) (Nat.beq v 5))
    (P.anyN 8 fun e => negK (Nat.beq (apL (rmC R e) v) v))

@[expose] noncomputable def uMaxAtK (EL : Nat → Nat) (UW a : Nat) : Bool :=
  P.impB (negK (inUK a)) (P.letB (lane UW 11 2047 a) fun w =>
    andB (Nat.blt w 1080) (andB (fix5K (EL w)) (P.letB (apL (EL w) a) fun ga =>
      andB (negK (inUK ga)) (andB (negK (inUK (Nat.xor ga a)))
        (P.allN 64 fun v => orB (orB (inUK v) (inUK (Nat.xor v a)))
          (orB (inUK (Nat.xor v (Nat.xor ga a))) (inUK (Nat.xor v ga))))))))

end CFSG.KC.Hall82K
